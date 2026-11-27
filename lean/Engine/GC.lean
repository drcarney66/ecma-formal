module

public import Engine.Machine

@[expose] public section

/-!
# Mark-and-sweep garbage collection over `ChunkedHeap`

Physical store garbage collection (`collectCfg`, `runGC`, `dispatchGC`) for `--gc` in `ecma-run` and the `"gc"`
request in `ecma-dbg`. Collection reclaims unreachable cells in `State.heap` (`ChunkedHeap.sweep`) without changing
any live cell's monotonic `Addr` (`Nat`) or touching `Ecma` / `Engine.implements`:

- Roots: caller-supplied `extraRoots` (`Engine.Host.Cells`: `out` and `realm`), the control (`Cfg.ctl`), the active
  frames (`Cfg.frames`, plus any enclosing sub-run frames/controls passed by the debugger), the execution context
  stack (`State.stack`), `resumed`, `suspended`, `agent`, `waiterLists`, `critical`, `shared`, `evalSteps`, `passed`,
  suspended generator/async frames (`State.frames`), and the live entries of `State.hostLog` (untaken scheduled jobs,
  non-job host hooks such as loaded modules and agent reports, and agent-cluster choices).
- Sweep: `ChunkedHeap.sweep` clears unmarked slots and drops completely empty 4096-cell chunks to `none`, keeping
  `heap.next` monotonic so every live address and future allocation address is unchanged.
-/

namespace Engine.GC

open Ecma Ecma.Machine Engine.Machine

abbrev F := Engine.Impl

/-- Summary of one mark-and-sweep cycle. -/
structure Stats where
  liveBefore : Nat
  liveAfter : Nat
  collected : Nat
  totalAllocated : Nat
  deriving Repr, BEq, Inhabited

/-- Mark state: `keep` indexed by `Addr < next`, and `work` holding marked addresses whose cell contents still
need scanning. Every address `< next` is pushed onto `work` at most once. -/
structure Mark where
  keep : Array Bool
  work : Array Nat

@[inline] def markAddr (next : Nat) (m : Mark) (a : Nat) : Mark :=
  if h : a < m.keep.size then
    if m.keep[a] then m
    else { keep := m.keep.set a true, work := if a < next then m.work.push a else m.work }
  else m

mutual
def markVal (next : Nat) (m : Mark) : Val F → Mark
  | .obj a | .ref a => markAddr next m a
  | .comp _ v g => markVal next (markVal next m v) g
  | .clo _ caps => markValList next m caps
  | .ty _ _ _ env => markValList next m env
  | .cond _ _ _ _ env => markValList next m env
  | .tuple vs => markValList next m vs
  | _ => m

def markValList (next : Nat) (m : Mark) : List (Val F) → Mark
  | [] => m
  | v :: vs => markValList next (markVal next m v) vs
end

@[inline] def markValArray (next : Nat) (m : Mark) (vs : @& Array (Val F)) : Mark :=
  vs.foldl (markVal next) m

def markEntries {K : Type} (next : Nat) (m : Mark) (es : @& Array (Option (K × Val F))) : Mark :=
  es.foldl (fun m e => match e with
    | some (_, v) => markVal next m v
    | none => m) m

def markRec (next : Nat) (m : Mark) (r : @& F.Rec (Val F)) : Mark :=
  markEntries next m (Engine.Model.WMap.entries (K := FieldId) r)

def markProps (next : Nat) (m : Mark) (p : @& F.Props (Val F)) : Mark :=
  markEntries next m (Engine.Model.WMap.entries (K := Array UInt16 ⊕ (Nat × Option (Array UInt16))) p)

def markCell (next : Nat) (m : Mark) : Cell F → Mark
  | .record _ fs => markRec next m fs
  | .list xs _ => markValArray next m xs
  | .block _ | .charSet _ => m
  | .object sl ps => markProps next (markRec next m sl) ps
  | .env _ fs bs => markProps next (markRec next m fs) bs

def markTarget (next : Nat) (m : Mark) : Target F → Mark
  | .sdo _ _ => m
  | .alg _ pre => markValList next m pre
  | .cmethod _ r => markVal next m r
  | .clo _ caps => markValList next m caps

def markFin (next : Nat) (m : Mark) : Fin F → Mark
  | .target t => markTarget next m t
  | .setIndexVal a xs _ => markValArray next (markAddr next m a) xs
  | .setBlockVal a _ => markAddr next m a
  | .jobRan _ _ job => markVal next m job
  | .jobKept _ v job => markVal next (markVal next m v) job
  | _ => m

def markScope (next : Nat) (m : Mark) : Scope F → Mark
  | .nodes _ _ => m
  | .passed outer inner => markValList next (markValList next m outer) inner

def markIterSt (next : Nat) (m : Mark) : IterSt F → Mark
  | .each a _ _ | .keys a _ => markAddr next m a
  | _ => m

def markKont (next : Nat) (m : Mark) : Kont F → Mark
  | .args f done _ => markValList next (markFin next m f) done
  | .all _ xs => markValList next m xs
  | .bind v => markVal next m v
  | .scope sc => markScope next m sc
  | .loop l | .test l => markIterSt next m l.st
  | .tstep _ _ _ key env _ _ _ => markValList next (markVal next m key) env
  | _ => m

def markFrame (next : Nat) (m : Mark) (f : Frame F) : Mark :=
  f.konts.foldl (markKont next) (markValArray next m f.slots)

def markFrames (next : Nat) (m : Mark) (fs : List (Frame F)) : Mark :=
  fs.foldl (markFrame next) m

def markCall (next : Nat) (m : Mark) : Call F → Mark
  | .alg _ vs | .sdo _ _ vs | .callAt _ _ vs | .prim _ vs => markValList next m vs
  | .clo _ caps vs => markValList next (markValList next m caps) vs
  | .cmethod _ r vs => markValList next (markVal next m r) vs
  | .sort _ v | .covered _ v => markVal next m v
  | .tstep _ _ _ key env => markValList next (markVal next m key) env
  | .early _ _ _ | .earlyRow _ _ _ | .jobs _ => m

def markCtl (next : Nat) (m : Mark) : Ctl F → Mark
  | .invoke call => markCall next m call
  | .loop _ l => markIterSt next m l.st
  | .val v | .ret v | .esc v => markVal next m v
  | .op _ | .code _ | .done => m

/-- Marks the values in `hostLog` that future host operations can still inspect:
- For `.hook` calls: `active`, `realm` and `answer` always; for scheduled jobs that have already been taken,
  `args.tail` (`realm`, read by `jobAgents`) without pinning the completed job closure `args.head`; for untaken jobs
  and non-job hooks (such as `HostLoadImportedModule` and `$262.agent` reports), all of `args`.
- For `.choice` calls: `HostSelectAgent`, `SuspendAgentUntil` and `WakeAgent` (agent-cluster state), skipping
  per-step `ForInStep` history Lists and `SortStep` tuples. -/
def markHostLog (next : Nat) (m : Mark) (log : List (HostCall F)) : Mark := Id.run do
  let len := log.length
  if len == 0 then return m
  let mut taken := Array.replicate len false
  for e in log do
    match e with
    | .next (some j) _ =>
      if j < len then taken := taken.set! j true
    | .choice q _ (.math j) =>
      if q == Known.pAgentNextJob then
        if let some k := Engine.Model.MathVal.idx j then
          if k < len then taken := taken.set! k true
    | _ => pure ()
  let mut m := m
  let mut idx := 0
  for e in log do
    let k := len - 1 - idx
    idx := idx + 1
    match e with
    | .hook _ args act rlm ans =>
      let argsToMark := if taken.getD k false && e.schedulesJob then args.tail else args
      m := markVal next (markVal next (markVal next (markValList next m argsToMark) act) rlm) ans
    | .choice q args ans =>
      if q == Known.pHostSelectAgent || q == Known.pSuspendAgentUntil || q == Known.pWakeAgent then
        m := markVal next (markValList next m args) ans
    | _ => pure ()
  return m

def markState (next : Nat) (m : Mark) (s : @& State F) : Mark := Id.run do
  let mut m := markValArray next m s.stack
  m := markVal next m s.resumed
  m := markVal next m s.suspended
  m := markVal next m s.agent
  for (b, _, w) in s.waiterLists do
    m := markAddr next (markAddr next m b) w
  for w in s.critical do
    m := markAddr next m w
  for b in s.shared do
    m := markAddr next m b
  for (_, v) in s.evalSteps do
    m := markVal next m v
  m := markValList next m s.passed
  m := markHostLog next m s.hostLog
  for (ctx, frs) in s.frames do
    m := markFrames next (markAddr next m ctx) frs
  return m

/-- Drains `m.work` over `heap`. Because `markAddr` sets `keep[a] := true` before pushing `a < next`, at most
`next` addresses can ever be pushed onto `work`. -/
def drain (next : Nat) (heap : @& Engine.Model.ChunkedHeap (Cell F)) (m : Mark) : Mark := Id.run do
  let mut m := m
  for _ in [0:next] do
    if h : m.work.size > 0 then
      let a := m.work[m.work.size - 1]
      m := { m with work := m.work.pop }
      if let some cell := heap.get a then
        m := markCell next m cell
    else
      break
  return m

/-- Runs one physical mark-and-sweep collection on configuration `c`, preserving `extraRoots` and any outer
sub-run `extraFrames` / `extraCtls`. -/
def collectCfg (extraRoots : @& Array Nat) (c : Cfg F)
    (extraFrames : List (Frame F) := []) (extraCtls : List (Ctl F) := []) : Stats × Cfg F :=
  let ⟨s, frames, ctl⟩ := c
  let next := s.heap.next
  let liveBefore := s.heap.live
  if next == 0 then
    ({ liveBefore := 0, liveAfter := 0, collected := 0, totalAllocated := 0 }, ⟨s, frames, ctl⟩)
  else
    let m : Mark := { keep := Array.replicate next false, work := Array.mkEmpty (min next 1024) }
    let m := extraRoots.foldl (markAddr next) m
    let m := markCtl next m ctl
    let m := extraCtls.foldl (markCtl next) m
    let m := markFrames next m frames
    let m := markFrames next m extraFrames
    let m := markState next m s
    let m := drain next s.heap m
    let (collected, heap') := s.heap.sweep m.keep
    let liveAfter := heap'.live
    let stats : Stats := {
      liveBefore
      liveAfter
      collected
      totalAllocated := next
    }
    (stats, ⟨{ s with heap := heap' }, frames, ctl⟩)

/-- Collects unreachable cells in a quiescent `State Impl`. -/
def collectState (extraRoots : @& Array Nat) (s : State F) : Stats × State F :=
  let (st, c) := collectCfg extraRoots { s, frames := [], ctl := .done }
  (st, c.s)

/-- Minimum live-cell threshold before automatic GC triggers (unless `maxCells` is smaller). -/
def minGCThreshold : Nat := 65536

/-- Initial live-cell threshold for a run under `maxCells`. -/
def initThreshold (maxCells : Option Nat) : Nat :=
  match maxCells with
  | some mc => min minGCThreshold (max 4096 (mc / 2))
  | none => minGCThreshold

/-- Next live-cell threshold after a collection leaving `liveAfter` live cells. -/
def nextThreshold (maxCells : Option Nat) (liveAfter : Nat) : Nat :=
  let grow := max minGCThreshold (liveAfter * 2)
  match maxCells with
  | some mc =>
    if liveAfter + 4096 ≤ mc then min grow mc
    else if liveAfter ≤ mc then mc + 1
    else grow
  | none => grow

/-- `Engine.Machine.runT` with adaptive mark-and-sweep garbage collection (`--gc`). -/
partial def runGC (E : Setup) (units : Thunk Units) (ob : Obs) (extraRoots : @& Array Nat)
    (nextGC : Nat) (c : Cfg F) : Final F :=
  let (nextGC, c) :=
    if c.s.heap.live ≥ nextGC then
      let (st, c) := collectCfg extraRoots c
      (nextThreshold E.maxCells st.liveAfter, c)
    else (nextGC, c)
  match stepObs E units ob c with
  | .inl c => runGC E units ob extraRoots nextGC c
  | .inr f => f

/-- Dispatcher using `runGC` on every machine run. -/
def dispatchGC (E : Setup) (units : Thunk Units) (ob : Obs) (extraRoots : Array Nat) : Engine.Host.Runner :=
  let initGC := initThreshold E.maxCells
  dispatchBy E (runGC E units ob extraRoots initGC)

end Engine.GC
