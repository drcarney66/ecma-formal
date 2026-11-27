module

public import Debugger.Machine.View
public import Engine.Run
public import Engine.GC

@[expose] public section

/-!
# The debugger's adapter to the machine: the run

`runW` is `Engine.Machine.runT` with the trace replaced by the step hook `atStep`: before each
transition it asks the session (`Debugger.Session.tick`) whether to look closer, and only then whether
to pause (`consider`), with the step entered and the depth. A sub-run (a leaf's call, a predicate
the model chooses over) is `runW` under its parent: the frames and control of the configuration
whose step started it, never its state, which the step goes on writing. So a pause anywhere sees
the whole spec stack: the configuration's frames, then its parents'. A run that ends in a stop
calls `atStop` with its parent-free view of the configuration before the stopping transition. A run
that ends in a transfer (a generator's or async body's suspension or resumption) calls `atXfer`,
which keeps its frames for the context it suspends: they live on in the state's `State.frames`, and
the JS stack (`Debugger.JSStack`) walks them as the frames of that context.

The hooks' meaning is to continue (`k c`, `k ()`), and their implementation (`implemented_by`)
consults the session in between. The implementation keeps no
reference to the configuration once it continues, so that the step still updates it in place.

The names and frame views are `Debugger.Machine.View`'s.
-/

namespace Debugger.Machine

open Ecma Ecma.Machine

/-- The step `pa` enters: its algorithm and path. -/
def enteredAt (pa : Parent) : Option (AlgId × List Nat) :=
  match pa.ctl, pa.frames with
  | .code (.site _ :: _), f :: _ => some (f.alg, f.path)
  | _, _ => none

/-- A configuration's frames and control as the debugger sees them: where the control enters a step, the
innermost frame is already at that step's path. -/
def Parent.of (c : Cfg F) : Parent :=
  match c.ctl, c.frames with
  | .code (.site p :: _), f :: fs => ⟨{ f with path := p } :: fs, c.ctl⟩
  | ctl, fs => ⟨fs, ctl⟩

/-- The frames of the parents. -/
def parentsDepth (ps : List Parent) : Nat := ps.foldl (fun n p => n + p.frames.length) 0

/-- The frames the debugger shows: not the driver's own (the algorithm that runs the program, and the job loop's
frame that holds it or the host's idle step). -/
def shown (fs : List (Frame F)) : List (Frame F) :=
  fs.filter fun f => !(Engine.Host.driverAlg f.alg || f.konts.any fun
    | .args (.idleRan ..) _ _ => true
    | _ => false)

/-- The depth of `c` under the parents `ps`: all their frames and its own. -/
def depth (ps : List Parent) (c : Cfg F) : Nat := parentsDepth ps + (shown c.frames).length

/-- The pause at `c`: its frames, then those saved for the
contexts on the stack (`saved`); `base` contexts were on the stack when the root's run started. -/
def paused (P : Prog) (ps : List Parent) (pa : Parent) (c : Cfg F)
    (base : Nat) : Paused :=
  let saved := c.s.frames.map fun (a, fs) => (Show.addr a, fun (_ : Unit) => views P [] fs (.val .absent))
  { frames := fun _ => wholeStack saved (stackAddrs c.s) (views P ps (shown pa.frames) pa.ctl), state := some c.s,
    depth := depth ps c, entered := enteredAt pa, base }

/-- `c` applies `?` to a throw completion: its escape passes a callee's on. -/
@[inline] def rethrows (c : Cfg F) : Bool :=
  match c.ctl, c.frames with
  | .val (.comp t _ _), f :: _ => match f.konts with
    | .args (.leaf .q) [] [] :: _ => t == Known.eThrow
    | _ => false
  | _, _ => false

/-- The control carries a throw completion: a value, a return or an escape of one. -/
@[inline] def carriesThrow : Ctl F → Bool
  | .val (.comp t _ _) | .ret (.comp t _ _) | .esc (.comp t _ _) => t == Known.eThrow
  | _ => false

/-- The depth a transition from `c` leaves the control at: a return's caller's, else `c`'s own. -/
@[inline] def carryDepth (ps : List Parent) (c : Cfg F) : Nat :=
  match c.ctl with
  | .ret _ => depth ps c - 1
  | _ => depth ps c

/-- Outward from a frame on the span [lo, hi) of parse `k`, to the first frame with a node of `k`
that is not a non-statement node of that span: whether its span differs (`some true`) or it is a
statement node of that span (`some false`); none if there is none. -/
def scanOuter (k lo hi : Nat) : List (Frame F) → Option Bool
  | [] => none
  | f :: fs => match f.node with
    | some (.mk k' lo' hi' _ nt _ _ _) =>
      if k' != k then scanOuter k lo hi fs
      else if lo' != lo || hi' != hi then some true
      else if names.stmtNts.contains nt then some false
      else scanOuter k lo hi fs
    | none => scanOuter k lo hi fs

/-- The node of the step `c` enters (under the parents `ps`), and whether the step is a statement
boundary: step 1 of a statement row, with no outer statement frame on its span before a frame on
another span of its parse. -/
def stepNode (ps : List Parent) (pa : Parent) : Option StepNode :=
  match pa.ctl, pa.frames with
  | .code (.site _ :: _), f :: outer => match f.node with
    | some (.mk k lo hi _ nt _ _ _) =>
      let boundary := f.path == [1] && names.stmtRows.contains (f.alg.clause, f.alg.idx) &&
        ((scanOuter k lo hi outer).orElse fun _ => ps.findSome? fun p => scanOuter k lo hi p.frames).getD true
      some { stamp := k, lo, hi, nt, boundary }
    | none => none
  | _, _ => none

/-- The nodes of the frames of `c` and of the parents `ps`, innermost first. -/
def frameNodes (ps : List Parent) (c : Cfg F) : List F.Node :=
  c.frames.filterMap (·.node) ++ ps.flatMap fun p => p.frames.filterMap (·.node)

/-- The contexts on the stack if `c` starts a run of the root (no parents, no frames) or a Job of the job loop (the
host's preparation has pushed its context), else none. -/
def rootContexts (ps : List Parent) (c : Cfg F) : Option Nat :=
  match ps, c.frames, c.ctl with
  | [], [], .invoke _ => some c.s.stack.size
  | [], [f], .invoke (.clo ..) => match f.konts with
    | [.args (.jobRan ..) [] []] => some c.s.stack.size
    | _ => none
  | [], [f], .invoke (.alg ..) => match f.konts with
    | [.args (.idleRan ..) [] []] => some c.s.stack.size
    | _ => none
  | _, _, _ => none

/-! The hooks. -/

unsafe def atStep.impl (P : Prog) (ps : List Parent) (pa : Parent) (n : Nat) (c : Cfg F) (k : Cfg F → Out F) : Out F :=
  unsafeBaseIO do
    noteRoot (rootContexts ps c)
    let isStep := match c.ctl, c.frames with
      | .code (.site _ :: _), f :: _ => !Engine.Host.driverAlg f.alg
      | _, _ => false
    let (esc, throwing) := match c.ctl with
      | .esc (.comp t _ _) => (true, t == Known.eThrow)
      | .esc _ => (true, false)
      | _ => (false, false)
    let carried := fun (_ : Unit) => (carriesThrow c.ctl, carryDepth ps c, if ps.isEmpty then some n else none)
    let look ← session.modifyGet (·.tick isStep esc throwing (rethrows c) carried c.s.parses)
    if look != Look.no then
      let ss ← session.get
      let cfgRef ← IO.mkRef (none : Option (Cfg F))
      let collect : Array Nat → IO (GCStats × State F × List FrameView) := fun extraRoots => do
        let cur0 := (← cfgRef.swap none).getD c
        let (st, cur1) := Engine.GC.collectCfg extraRoots cur0 (ps.flatMap (·.frames)) (ps.map (·.ctl))
        cfgRef.set (some cur1)
        let paCur := Parent.of cur1
        let p1 := paused P ps paCur cur1 ss.rootBase
        let stats : GCStats := {
          liveBefore := st.liveBefore
          liveAfter := st.liveAfter
          collected := st.collected
          heapSize := st.totalAllocated
        }
        return (stats, cur1.s, p1.frames ())
      let p := fun (_ : Unit) => { paused P ps pa c ss.rootBase with collect := some collect }
      if look == Look.consider then
        (consider (enteredAt pa) (fun _ => depth ps c) (fun _ => stepNode ps pa) (fun _ => c.s.stack.size) (fun _ => frameNodes ps c)
          c.s.parses p).catchExceptions fun _ => pure ()
      else
        let v := match c.ctl with
          | .esc v => v
          | _ => .absent
        (onThrow v (look == Look.rethrow) p).catchExceptions fun _ => pure ()
      let c := (← cfgRef.swap none).getD c
      return k c
    return k c

/-- Before the transition from `c` (under the parents `ps`, `n` transitions left): `k c`, the
session consulted. -/
@[implemented_by atStep.impl]
def atStep (_P : Prog) (_ps : List Parent) (_pa : Parent) (_n : Nat) (c : Cfg F) (k : Cfg F → Out F) : Out F := k c

unsafe def atStop.impl (P : Prog) (ps : List Parent) (pa : Parent) (r : Stop) (k : Unit → Final F) : Final F :=
  unsafeBaseIO do
    let p : Unit → Paused := fun _ =>
      let d := parentsDepth ps + (shown pa.frames).length
      { frames := fun _ => views P ps (shown pa.frames) pa.ctl, state := none, depth := d, entered := none, stop? := some (Engine.SpecRun.stopName r) }
    (onStop p).catchExceptions fun _ => pure ()
    return k ()

/-- A run (under the parents `ps`) stopped by `r` in the transition from `pa`: `k ()`, the session
consulted. -/
@[implemented_by atStop.impl]
def atStop (_P : Prog) (_ps : List Parent) (_pa : Parent) (_r : Stop) (k : Unit → Final F) : Final F := k ()

/-- The transition from `c` is a transfer: the value a suspended computation is passed is at its last operand. -/
def isXfer (c : Cfg F) : Bool :=
  match c.ctl, c.frames with
  | .val _, f :: _ => match f.konts with
    | .args (.transfer _) [_] [] :: _ => true
    | _ => false
  | _, _ => false

unsafe def atXfer.impl (o : Out F) : Out F := unsafeBaseIO do
  noteXfer
  return o

/-- `o`, the result of a transfer's transition, the session told. -/
@[implemented_by atXfer.impl]
def atXfer (o : Out F) : Out F := o

unsafe def noteW.impl (pa : Parent) (o : Out F) : Out F :=
  match o with
  | .inr (.stop _) | .inr (.todo _) => unsafeBaseIO do
    Engine.Machine.stopFrames.modify fun r => some (r.getD #[] ++ (pa.frames.map fun f => (f.alg, f.path)).toArray)
    return o
  | _ => unsafeBaseIO do
    if (← Engine.Machine.stopFrames.get).isSome then Engine.Machine.stopFrames.set none
    return o

/-- `o`, the result of the transition from `pa`'s configuration: `Machine.noteOut` from the frames
kept, so that a stop's site is recorded as `ecma-run` records it. -/
@[implemented_by noteW.impl]
def noteW (_pa : Parent) (o : Out F) : Out F := o

/-- A run under the parents `ps`, `n` numbering its transitions (a transfer skips a number, so that the session
sees the resumed context's transitions as another computation's): each transition through `atStep`, a stop through `atStop`, a transfer through
`atXfer`. With `sites`, a stop's frames are kept. -/
partial def runW (E : Engine.Machine.Setup) (sites : Bool) (ps : List Parent) (n : Nat) (c : Cfg F)
    (gc : Option (Array Nat × Nat) := none) : Final F :=
  let (gc, c) := match gc with
    | some (roots, nextGC) =>
      if c.s.heap.live ≥ nextGC then
        let (st, c) := Engine.GC.collectCfg roots c (ps.flatMap (·.frames)) (ps.map (·.ctl))
        (some (roots, Engine.GC.nextThreshold E.maxCells st.liveAfter), c)
      else (some (roots, nextGC), c)
    | none => (none, c)
  if E.full c then .stop .implLimit else
  let X := E.X
  let pa := Parent.of c
  let xfer := isXfer c
  let o := atStep X.P ps pa n c fun c => Engine.Machine.stepA E c
  let o := if xfer then atXfer o else o
  let o := if sites then noteW pa o else o
  match o with
  | .inl c => runW E sites ps (if xfer then n + 2 else n + 1) c gc
  | .inr (.stop r) => atStop X.P ps pa r fun _ => .stop r
  | .inr f => f

/-- `Engine.Machine.dispatch` over `runW`: every entry a watched run. -/
def dispatchW (E : Engine.Machine.Setup) (sites : Bool) (gcRoots : Option (Array Nat) := none) : Engine.Host.Runner :=
  let gc := gcRoots.map (·, Engine.GC.initThreshold E.maxCells)
  Engine.Machine.dispatchBy E (runW E sites [] 0 · gc)

end Debugger.Machine
