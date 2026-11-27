module

public import Debugger.Protocol
public import Debugger.Heap
public import Debugger.JSStack
public import Std.Data.HashMap

@[expose] public section

/-!
# The debugger's session

What a run's step hook consults: the stepping mode, the breakpoints, the filters and the
counters, and the channel the protocol (`Debugger.Protocol`) runs on. Engine-neutral: an engine's
adapter (`Debugger.Machine`) asks `tick` at each transition, which only counts and compares; where it
answers yes, the adapter calls `consider` with the step entered and the depth, and only a pause
builds a `Paused` record of frame views (`FrameView`) and the state. At a pause the session sends
the lines `print` wrote since the last pause (`output`), then `stopped` with the difference from
the previous pause's state (`Debugger.Heap.Diff`; the session keeps that state, so the run's first
write after the pause copies the heap's array once), and serves requests from the record until one
resumes the run: `stackTrace`, `scopes` and `variables` (`Debugger.View`, `Debugger.Heap`), `specHeap`,
`specState` and `specDiff`. `specAlgorithm`, an algorithm's listing (`Names.algorithm`), and `source`,
a source's text, are served at any phase.

The sources (`Sources`): the program (a bundle's entry module), a bundle's other modules, and the
eval and Function code parsed after `arm`, which `noteParses` adds or adopts as the parses are
made; statement boundaries, JS positions and line breakpoints count the nodes of every source's
parses.

The filters: `stop` (a run ends in a model stop), `throw` (a throw completion starts to escape:
not by `?` passing on a callee's, nor the completion a pause has shown passing out of a run) and
`debugger` (a breakpoint on the DebuggerStatement's Evaluation, step 1).

Requests are read only at a pause. A run is paused from outside through the poll channel (a file
or a device, `--dbg-poll`): every `pollEvery` transitions `consider` reads its first byte, and a
nonzero one pauses with reason `pause`; resuming writes it back to 0. A client sets it with a
`pause` request, which the engine then reads and answers at that pause, after `stopped`.

The run's root opens the session (`openOn`), serves requests until the program is launched and
configured (`awaitLaunch`), sets the realm up, arms the session (`arm`: setup's steps pause only
with `stopInSetup`), runs the program and reports its end (`finish`).
-/

namespace Debugger

open Ecma

/-- When the run pauses next: at a breakpoint only (`run`), at the next step (`stepIn`), at the next
step at most (`next`) or less than (`out`) the depth, at the next transition (`instr`); by statement,
with `d` the execution context stack's length: at the next boundary (`stmtIn`), at the next boundary
at most `d` deep or JS-positioned step less deep (`stmtNext`), at the next JS-positioned step less
than `d` deep (`stmtOut`); once a throw escapes, at a boundary only (at most, less than `d` deep). -/
inductive Mode where
  | run
  | stepIn
  | next (d : Nat)
  | out (d : Nat)
  | instr
  | stmtIn
  | stmtNext (d : Nat)
  | stmtOut (d : Nat)

/-- A line breakpoint: its id, its source's `sourceReference` (0: the program), the line and column
asked for, and the statement it resolved to (none while the statement table is pending, or where no
statement follows the line). -/
structure LineBp where
  id : Nat
  src : Nat := 0
  line : Nat
  column : Option Nat := none
  stmt : Option StmtPos := none

structure Session where
  mode : Mode := .run
  /-- the reason a pause by `mode` reports: `entry` until the first, then `step` -/
  reason : String := "step"
  /-- breakpoints: by algorithm (clause, index), the step paths -/
  bps : Std.HashMap (Nat × Nat) (List (List Nat)) := {}
  stopFilter : Bool := false
  throwFilter : Bool := false
  /-- the `debugger` filter: the algorithms of the DebuggerStatement's Evaluation, by (clause, index) -/
  debuggerAt : List (Nat × Nat) := []
  /-- the line breakpoints, and the resolved ones' ids by their source and statement's start in it -/
  lineBps : Array LineBp := #[]
  lineAt : Std.HashMap (Nat × Nat) (List Nat) := {}
  nextBpId : Nat := 1
  /-- the sources' statement tables, by `sourceReference`: the program's once its root Parse Node is
  known, another's when a breakpoint asks for it -/
  tables : Std.HashMap Nat (Array StmtPos) := {}
  /-- the control escaped at the last transition -/
  wasEsc : Bool := false
  /-- the last transition applied `?` to a throw completion -/
  wasRethrow : Bool := false
  /-- a throw escaped in `stmtNext` or `stmtOut` since the last boundary, and is not yet consumed -/
  stmtThrow : Bool := false
  /-- the least depth a transition carrying that throw completion had -/
  throwMin : Nat := 0
  /-- the transition's number in the top-level run that last carried it -/
  throwRun : Option Nat := none
  /-- the throw completion the `throw` filter last paused at (kept: it does not pause again) -/
  lastThrow : Option (Val F) := none
  armed : Bool := false
  stopInSetup : Bool := false
  transitions : Nat := 0
  steps : Nat := 0
  /-- a stop was shown, and no transition has run since: its unwinding through the runs -/
  stopShown : Bool := false
  seq : Nat := 1
  names : Names := {}
  inp : Option IO.FS.Stream := none
  out : Option IO.FS.Stream := none
  launch : Option Req := none
  configured : Bool := false
  srcs : Sources := {}
  /-- the eval and Function sources so far -/
  evals : Nat := 0
  functions : Nat := 0
  /-- the parses made when the hooks last looked -/
  parsesSeen : Nat := 0
  /-- the poll channel's path: its first byte nonzero asks the run to pause -/
  poll : Option System.FilePath := none
  /-- the List cell `print` appends its lines to, and how many of them were sent -/
  printCell : Option Nat := none
  printed : Nat := 0
  /-- the host's external root cells (`out`, `realm`) preserved across manual `gc` requests -/
  hostCells : Array Nat := #[8, 9]
  /-- the previous pause's state and slots, and the differences from them at this pause -/
  prev : Option (State F) := none
  prevSlots : SlotsSeen := []
  diff : Option Diff := none
  changed : List (List Nat) := []
  /-- the transitions when the last transfer was seen -/
  xferAt : Option Nat := none
  /-- the contexts on the stack when the running root run started -/
  rootBase : Nat := 0

instance : Nonempty Session := ⟨{}⟩

initialize session : IO.Ref Session ← IO.mkRef {}

/-- The transitions between two reads of the poll channel. -/
def pollEvery : Nat := 4096

/-- Whether the hooks look at all: armed, or pausing in setup too. -/
@[inline] def Session.live (s : Session) : Bool := s.armed || s.stopInSetup

/-- The poll channel is to be read at this transition. -/
@[inline] def Session.pollDue (s : Session) : Bool := s.poll.isSome && s.transitions % pollEvery == 0

/-- What `tick` asks of the adapter: nothing, `consider` the configuration, or pause at it with
the `throw` filter (`throw`: a completion made there; `rethrow`: one `?` raised). -/
abbrev Look := Nat

def Look.no : Look := 0
def Look.consider : Look := 1
def Look.throw : Look := 2
def Look.rethrow : Look := 3

/-- A top-level run's transition numbered `r` is not the next of the run the throw was last carried in. -/
@[inline] def Session.otherRun (s : Session) (r : Option Nat) : Bool :=
  match r, s.throwRun with
  | some n, some m => n != m + 1
  | _, _ => false

/-- `stmtThrow`, `throwMin` and `throwRun` after a transition (`carried`: whether its control
carries a throw completion, its depth, and the transition's number in its run if it is a top-level
run): set by a throw escaping in `stmtNext` or `stmtOut`; cleared by a transition less deep than
every one that carried the throw that carries none, or by one of another run (a resumed context's,
whose depths do not compare) that carries none: the throw was consumed. -/
@[inline] def Session.throwAfter (s : Session) (esc throwing : Bool) (carried : Unit → Bool × Nat × Option Nat) :
    Bool × Nat × Option Nat :=
  let stmtMode := match s.mode with
    | .stmtNext _ | .stmtOut _ => true
    | _ => false
  if esc && throwing && stmtMode then
    let (_, d, r) := carried ()
    if s.stmtThrow && !s.otherRun r then (true, min s.throwMin d, r.or s.throwRun) else (true, d, r)
  else if !s.stmtThrow then (false, s.throwMin, s.throwRun)
  else
    let (t, d, r) := carried ()
    if s.otherRun r then (t, d, r)
    else if t then (true, min s.throwMin d, r.or s.throwRun)
    else (d ≥ s.throwMin, s.throwMin, r.or s.throwRun)

/-- A transition (`isStep`: it enters a step; `esc`: its control escapes, `throwing`: with a throw
completion; `rethrow`: it applies `?` to a throw completion; `carried`: whether its control carries
a throw completion, its depth, and a top-level run's transitions left; `parses`: the parses made so far), counted; whether the adapter
must look closer. -/
@[inline] def Session.tick (s : Session) (isStep esc throwing rethrow : Bool) (carried : Unit → Bool × Nat × Option Nat)
    (parses : Nat) : Look × Session :=
  if !s.live then (Look.no, s)
  else
    let steps := if isStep then s.steps + 1 else s.steps
    let thrown := s.throwFilter && throwing && !s.wasEsc
    let raised := s.wasRethrow
    let (stmtThrow, throwMin, throwRun) := s.throwAfter esc throwing carried
    let s := { s with transitions := s.transitions + 1, steps, stopShown := false, wasEsc := esc,
                      wasRethrow := rethrow, stmtThrow, throwMin, throwRun }
    let look := match s.mode with
      | .instr => true
      | .run => isStep && (!s.bps.isEmpty || !s.debuggerAt.isEmpty || !s.lineBps.isEmpty)
      | _ => isStep
    (if thrown then (if raised then Look.rethrow else Look.throw)
      else if look || s.pollDue || parses != s.parsesSeen then Look.consider else Look.no, s)

/-! The channel. -/

/-- Sends the message `mk seq`, numbered by the session. -/
def emit (mk : Nat → Json) : IO Unit := do
  let (n, out) ← session.modifyGet fun s => ((s.seq, s.out), { s with seq := s.seq + 1 })
  if let some o := out then
    o.putStrLn (mk n).render
    o.flush

def respond (r : Req) (body : Json := .obj #[]) : IO Unit := emit (response · r body)

def refuse (r : Req) (msg : String) : IO Unit := emit (errorResponse · r msg)

/-- The next request; none at the end of the input. A line that is not one is answered with an
`output` event on the console. -/
partial def recv : IO (Option Req) := do
  let some i := (← session.get).inp | return none
  let line ← i.getLine
  if line.isEmpty then return none
  let line := line.trimAscii.toString
  if line.isEmpty then return ← recv
  match Json.parse line >>= Req.ofJson with
  | .ok r => return some r
  | .error e =>
    emit (event · "output" (Json.mk [("category", "console"), ("output", s!"bad request: {e}\n")]))
    recv

/-! Requests. -/

/-- `setSpecBreakpoints`: the breakpoints replaced; each `{alg, path?}` resolved. -/
def setSpecBreakpoints (r : Req) : IO Unit := do
  let s ← session.get
  let bs := ((r.arg? "breakpoints").bind Json.arr?).getD #[]
  let (m, replies) := bs.foldl (init := (({} : Std.HashMap (Nat × Nat) (List (List Nat))), #[]))
    fun (m, replies) b =>
      let alg := ((b.get? "alg").bind Json.str?).getD ""
      let pathText := (b.get? "path").bind Json.str?
      let path := match pathText with
        | some t => s.names.parsePath t
        | none => some [1]
      let algs := s.names.resolve alg
      match path, algs with
      | some p, _ :: _ =>
        let m := algs.foldl (fun m a => m.alter (a.clause, a.idx) fun ps => some (p :: ps.getD [])) m
        (m, replies.push (Json.mk [("verified", true), ("alg", alg), ("path", s.names.pathText p),
          ("resolved", .arr (algs.map fun a => .str s!"{s.names.secId a}#{a.idx}").toArray)]))
      | none, _ => (m, replies.push (Json.mk [("verified", false), ("alg", alg), ("message", "bad step path")]))
      | _, [] => (m, replies.push (Json.mk [("verified", false), ("alg", alg), ("message", "no such algorithm")]))
  session.modify ({ · with bps := m })
  respond r (Json.mk [("breakpoints", .arr replies)])

/-- `specAlgorithm` {secId, idx} or {alg} (as a breakpoint's, naming one algorithm): its listing. -/
def specAlgorithm (r : Req) : IO Unit := do
  let s ← session.get
  let alg := match (r.arg? "secId").bind Json.str?, (r.arg? "idx").bind Json.nat? with
    | some sec, some i => s!"{sec}#{i}"
    | some sec, none => sec
    | none, _ => ((r.arg? "alg").bind Json.str?).getD ""
  match s.names.resolve alg with
  | [a] => match s.names.algorithm a with
    | some l => respond r l.json
    | none => refuse r s!"no listing of {alg}"
  | [] => refuse r s!"no such algorithm {alg}"
  | as => refuse r s!"{alg} names {as.length} algorithms: give secId and idx"

/-- A line breakpoint as DAP's `Breakpoint`: verified where it resolved, at its statement's start;
pending before the statement table. -/
def LineBp.json (b : LineBp) (s : Session) : Json :=
  let src : List (String × Json) := match s.srcs.byRef? b.src with
    | some p => [("source", p.sourceJson)]
    | none => []
  match b.stmt, s.tables.get? b.src with
  | some e, _ => Json.mk ([("id", Json.nat b.id), ("verified", Json.bool true), ("line", .nat e.line), ("column", .nat e.column)] ++ src)
  | none, none => Json.mk [("id", .nat b.id), ("verified", false), ("line", .nat b.line), ("message", "pending")]
  | none, some _ => Json.mk [("id", .nat b.id), ("verified", false), ("line", .nat b.line), ("message", "no statement at or after this line")]

/-- The line breakpoints resolved against the table `t`. -/
def resolveBps (t : Array StmtPos) (bs : Array LineBp) : Array LineBp :=
  bs.map fun b => { b with stmt := resolveLine t b.line b.column }

/-- The resolved line breakpoints' ids by their source and statement start. -/
def bpIndex (bs : Array LineBp) : Std.HashMap (Nat × Nat) (List Nat) :=
  bs.foldl (init := {}) fun m b => match b.stmt with
    | some e => m.alter (b.src, e.lo) fun ids => some (b.id :: ids.getD [])
    | none => m

/-- Whether a request's `source` is the program's: by its path, where both have one. -/
def isProgramSource (r : Req) (s : Session) : Bool :=
  match ((r.arg? "source").bind (·.get? "path")).bind Json.str?, s.srcs.program.bind (·.path) with
  | some a, some b => a == b
  | _, _ => true

/-- The `sourceReference` of a request's source (`source.sourceReference`, else `sourceReference`):
code parsed by the run if one has it, else the program (0) by `isProgramSource`; none if unknown. -/
def reqSource (r : Req) (s : Session) : Option Nat :=
  match (((r.arg? "source").bind (·.get? "sourceReference")) <|> r.arg? "sourceReference").bind Json.nat? with
  | some ref => if ref == 0 then (if isProgramSource r s then some 0 else none) else (s.srcs.byRef? ref).map (·.ref)
  | none => if isProgramSource r s then some 0 else none

/-- The statement table of the source `ref`: kept, else built from its root node (not the program's,
which `noteTable` builds). -/
def tableOf (ref : Nat) : IO (Option (Array StmtPos)) := do
  let s ← session.get
  if let some t := s.tables.get? ref then return some t
  if ref == 0 then return none
  let some p := s.srcs.byRef? ref | return none
  let some root := p.root | return none
  let t := stmtTable s.names p root
  session.modify fun s => { s with tables := s.tables.insert ref t }
  return some t

/-- `setBreakpoints` {source, breakpoints: [{line, column?}]}: the source's line breakpoints replaced,
each with a new id; resolved against its statement table, else pending. -/
def setBreakpoints (r : Req) : IO Unit := do
  let s ← session.get
  let some ref := reqSource r s | return ← refuse r "unknown source"
  let asked := ((r.arg? "breakpoints").bind Json.arr?).getD #[]
  let bs := asked.zipIdx.map fun (b, i) =>
    { id := s.nextBpId + i, src := ref, line := ((b.get? "line").bind Json.nat?).getD 1, column := (b.get? "column").bind Json.nat? : LineBp }
  let bs := match ← tableOf ref with
    | some t => resolveBps t bs
    | none => bs
  let all := s.lineBps.filter (·.src != ref) ++ bs
  session.modify ({ · with lineBps := all, lineAt := bpIndex all, nextBpId := s.nextBpId + bs.size })
  let s ← session.get
  respond r (Json.mk [("breakpoints", .arr (bs.map (·.json s)))])

/-- `breakpointLocations` {source, line, endLine?}: the statements' starts on those lines. -/
def breakpointLocations (r : Req) : IO Unit := do
  let s ← session.get
  let some ref := reqSource r s | return ← refuse r "unknown source"
  let some t ← tableOf ref | return ← refuse r "pending"
  let line := ((r.arg? "line").bind Json.nat?).getD 1
  let endLine := ((r.arg? "endLine").bind Json.nat?).getD line
  let es := t.filter fun e => line ≤ e.line && e.line ≤ endLine
  respond r (Json.mk [("breakpoints", .arr (es.map fun e => Json.mk [("line", .nat e.line), ("column", .nat e.column)]))])

/-- The algorithm the `debugger` filter breaks in, at step 1. -/
def debuggerSecId : String := "sec-debugger-statement-runtime-semantics-evaluation"

/-- `setExceptionBreakpoints`: the filters replaced (`stop`, `throw`, `debugger`). -/
def setExceptionBreakpoints (r : Req) : IO Unit := do
  let fs := (((r.arg? "filters").bind Json.arr?).getD #[]).filterMap Json.str?
  let s ← session.get
  let debuggerAt := if fs.contains "debugger" then (s.names.resolve debuggerSecId).map fun a => (a.clause, a.idx) else []
  session.modify ({ · with stopFilter := fs.contains "stop", throwFilter := fs.contains "throw", debuggerAt })
  let ok := fun f => f == "stop" || f == "throw" || (f == "debugger" && !debuggerAt.isEmpty)
  respond r (Json.mk [("breakpoints", .arr (fs.map fun f => Json.mk [("verified", ok f)]))])

/-- `stackTrace` at a pause: the frames from `startFrame`, at most `levels` (all when 0); with
`view: "js"` the JS frames (`jsStackJson`) and the execution context stack's length. -/
def stackTrace (r : Req) (p : Paused) : IO Unit := do
  let s ← session.get
  let start := ((r.arg? "startFrame").bind Json.nat?).getD 0
  let levels := ((r.arg? "levels").bind Json.nat?).getD 0
  let page := fun {α : Type} (xs : List α) => if levels == 0 then xs.drop start else (xs.drop start).take levels
  if (r.arg? "view").bind Json.str? == some "js" then
    let fs := jsStackJson s.names s.srcs (p.frames ()) p.state p.base
    let ctxs : List (String × Json) := match p.state with
      | some st => [("contexts", .nat (stackList st).length)]
      | none => []
    respond r (Json.mk ([("stackFrames", .arr (page fs).toArray), ("totalFrames", .nat fs.length)] ++ ctxs))
  else
    let fs := (p.frames ()).zipIdx
    respond r (Json.mk [("stackFrames", .arr ((page fs).map fun (f, i) => f.json s.names s.srcs i).toArray),
      ("totalFrames", .nat fs.length)])

/-- `scopes` of the frame `frameId` at a pause. -/
def scopesReq (r : Req) (p : Paused) : IO Unit := do
  let id := ((r.arg? "frameId").bind Json.nat?).getD 0
  match (p.frames ())[id]? with
  | some f => respond r (scopes f id p.state.isSome)
  | none => refuse r s!"no frame {id}"

/-- `variables` of a scope or a cell at a pause; a List's elements paged by `start` and `count`. -/
def variablesReq (r : Req) (p : Paused) : IO Unit := do
  let s ← session.get
  let pg : Page := { start := ((r.arg? "start").bind Json.nat?).getD 0, count := (r.arg? "count").bind Json.nat? }
  let pg := if pg.count == some 0 then { pg with count := none } else pg
  match variables s.names s.srcs p s.prev s.changed (((r.arg? "variablesReference").bind Json.nat?).getD 0) pg with
  | .ok vs => respond r (Json.mk [("variables", .arr (vs.map Var.json).toArray)])
  | .error e => refuse r e

/-- `specHeap` {from, count, kind?}: the cells of an address range, each with a summary. -/
def specHeap (r : Req) (p : Paused) : IO Unit := do
  let s ← session.get
  let some st := p.state | return ← refuse r "no state at a stop"
  let lo := ((r.arg? "from").bind Json.nat?).getD 0
  let count := ((r.arg? "count").bind Json.nat?).getD 100
  respond r (heapJson s.names st lo count ((r.arg? "kind").bind Json.str?))

/-- `specState`: the state beside the heap, and the host / model group. -/
def specState (r : Req) (p : Paused) : IO Unit := do
  let s ← session.get
  let some st := p.state | return ← refuse r "no state at a stop"
  respond r (stateJson s.names st [("transitions", .nat s.transitions), ("steps", .nat s.steps)])

/-- `specDiff` {addr}: a cell at the previous pause and now. -/
def specDiff (r : Req) (p : Paused) : IO Unit := do
  let s ← session.get
  let some st := p.state | return ← refuse r "no state at a stop"
  let some a := (r.arg? "addr").bind Json.nat? | return ← refuse r "specDiff: no addr"
  match cellDiffJson s.names s.prev st a with
  | .ok j => respond r j
  | .error e => refuse r e

/-- The execution context stack's length at a pause (0 at a stop). -/
def contextsOf (p : Paused) : Nat := (p.state.map fun st => (stackList st).length).getD 0

/-- `source` {sourceReference} (or {source}): the source's text, by its `sourceReference`, else the
program's by its path. -/
def sourceReq (r : Req) : IO Unit := do
  let s ← session.get
  match (reqSource r s).bind s.srcs.byRef? with
  | some p => respond r (Json.mk [("content", .str (pointsText p.src)), ("mimeType", "text/javascript")])
  | none => refuse r "unknown source"

/-- Where requests are served: before the run, at a pause, or after the run. -/
inductive Phase where
  | setup
  | paused (p : Paused)
  | ended

/-- Ends the process after answering `disconnect`. -/
def disconnect (r : Req) : IO Unit := do
  respond r
  IO.Process.exit 0

/-- Refuses a request not served where it came: a run's request outside a pause, a second launch,
or an unknown one. -/
def refuseOutOfPlace (r : Req) : IO Unit :=
  if ["continue", "next", "stepIn", "stepOut", "stackTrace", "scopes", "variables", "pause", "specHeap", "specState",
      "specDiff", "gc"].contains r.command then
    refuse r "not paused"
  else if ["launch", "configurationDone"].contains r.command then refuse r "already launched"
  else refuse r s!"unknown request {r.command}"

/-- Serves `r`: the next `Phase`, and whether it resumes the run (at a pause) or completes the launch (before it). -/
def handle (ph : Phase) (r : Req) : IO (Phase × Bool) := do
  match r.command, ph with
  | "initialize", _ =>
    respond r capabilities
    emit (event · "initialized")
    return (ph, false)
  | "launch", .setup =>
    let entry := r.flag "stopOnEntry"
    let mode : Mode := if entry then .stepIn else .run
    let reason := if entry then "entry" else "step"
    session.modify fun s => { s with launch := some r, stopInSetup := r.flag "stopInSetup", mode, reason }
    respond r
    return (ph, (← session.get).configured)
  | "configurationDone", .setup =>
    session.modify ({ · with configured := true })
    respond r
    return (ph, (← session.get).launch.isSome)
  | "setSpecBreakpoints", _ => setSpecBreakpoints r; return (ph, false)
  | "setExceptionBreakpoints", _ => setExceptionBreakpoints r; return (ph, false)
  | "setBreakpoints", _ => setBreakpoints r; return (ph, false)
  | "breakpointLocations", _ => breakpointLocations r; return (ph, false)
  | "threads", _ => respond r threads; return (ph, false)
  | "specAlgorithm", _ => specAlgorithm r; return (ph, false)
  | "source", _ => sourceReq r; return (ph, false)
  | "stackTrace", .paused p => stackTrace r p; return (ph, false)
  | "scopes", .paused p => scopesReq r p; return (ph, false)
  | "variables", .paused p => variablesReq r p; return (ph, false)
  | "specHeap", .paused p => specHeap r p; return (ph, false)
  | "specState", .paused p => specState r p; return (ph, false)
  | "specDiff", .paused p => specDiff r p; return (ph, false)
  | "gc", .paused p =>
    match p.collect with
    | none => refuse r "no state at a stop"; return (ph, false)
    | some collect =>
      let s ← session.get
      let (stats, st', fs') ← collect s.hostCells
      let p' : Paused := { p with state := some st', frames := fun _ => fs' }
      let d := match s.prev with
        | some old => some (diff old st')
        | none => none
      session.modify ({ · with diff := d })
      respond r stats.json
      return (.paused p', false)
  | "pause", .paused _ => respond r; return (ph, false)
  | "disconnect", _ => disconnect r; return (ph, true)
  | cmd, .paused p =>
    let gran := (r.arg? "granularity").bind Json.str?
    let stmt := gran == some "statement"
    -- a statement `next` or `stepOut` where the pause has no JS position is a statement `stepIn`
    let srcs := (← session.get).srcs
    let jsHere := (p.frames ()).any fun f => f.node.any (srcs.knows ∘ nodeStamp)
    let mode? : Option Mode := match cmd with
      | "continue" => some .run
      | "next" => some (if !stmt then .next p.depth else if jsHere then .stmtNext (contextsOf p) else .stmtIn)
      | "stepIn" => some (if gran == some "instruction" then .instr else if stmt then .stmtIn else .stepIn)
      | "stepOut" => some (if !stmt then .out p.depth else if jsHere then .stmtOut (contextsOf p) else .stmtIn)
      | _ => none
    match mode? with
    | some m =>
      session.modify ({ · with mode := m, reason := "step", stmtThrow := false })
      respond r (if cmd == "continue" then Json.mk [("allThreadsContinued", true)] else .obj #[])
      return (ph, true)
    | none => refuseOutOfPlace r; return (ph, false)
  | _, _ => refuseOutOfPlace r; return (ph, false)

/-- Serves requests in `ph` until one resumes or launches (`some ph'`), or the input ends (`none`). -/
partial def serve (ph : Phase) : IO (Option Phase) := do
  let some r ← recv | return none
  let (ph', done) ← handle ph r
  if done then return some ph' else serve ph'

/-! The whole spec stack. -/

/-- The addresses of the contexts on the stack, the top first. -/
def stackAddrs (s : State F) : List Nat :=
  (stackList s).reverse.filterMap fun
    | .ref a => some (Show.addr a)
    | _ => none

/-- A pause's whole spec stack, innermost first: `visible`, the running computation's frames, then
the saved frames of each context on the stack (`ctxs`, the top first) that has them; runs numbered
from the outermost. -/
def wholeStack (saved : List (Nat × (Unit → List FrameView))) (ctxs : List Nat) (visible : List FrameView) :
    List FrameView :=
  let chains := visible :: ctxs.filterMap fun a => (saved.lookup a).map (· ())
  let runs := fun (fs : List FrameView) => fs.foldl (fun m f => max m (f.run + 1)) 0
  (chains.foldr (fun fs (acc, off) => (fs.map (fun f => { f with run := f.run + off }) ++ acc, off + runs fs))
    (([] : List FrameView), 0)).1

/-- A transfer happens in this transition: the next run of the root, if any, is its resumption. -/
def noteXfer : BaseIO Unit :=
  session.modify fun s => if !s.live then s else { s with xferAt := some s.transitions }

/-- A run of the root starts with `contexts` on the stack (if some), unless a transfer just started it. -/
def noteRoot : Option Nat → BaseIO Unit
  | some contexts => session.modify fun s => if s.xferAt == some s.transitions then s else { s with rootBase := contexts }
  | none => pure ()

/-! Pausing. -/

/-- The `stopped` event's body; `filter`: the exception filter that paused. -/
def stoppedBody (reason : String) (p : Paused) (s : Session) (filter : Option String := none) (hits : List Nat := []) : Json :=
  let top := (p.frames ()).head?
  let spec := Json.mk [("alg", (top.map (·.name)).getD ""), ("secId", (top.map (·.secId)).getD ""),
    ("idx", .nat ((top.map (·.alg.idx)).getD 0)), ("path", (top.map (·.path)).getD ""), ("text", (top.map (·.text)).getD ""),
    ("spectec", (top.map (·.spectec)).getD ""), ("depth", .nat p.depth),
    ("steps", .nat s.steps), ("transitions", .nat s.transitions)]
  let spec := match top.bind (·.reading) with
    | some r => spec.set "reading" r
    | none => spec
  let spec := match p.stop? with
    | some st => spec.set "stop" st
    | none => spec
  let spec := match filter with
    | some f => spec.set "filter" f
    | none => spec
  let spec := match s.diff with
    | some d => spec.set "diff" d.json
    | none => spec
  let body := Json.mk [("reason", reason), ("threadId", 1), ("allThreadsStopped", true), ("spec", spec),
    ("js", jsJson s.names s.srcs (p.frames ()) p.state)]
  let body := if hits.isEmpty then body else body.set "hitBreakpointIds" (.arr (hits.map Json.nat).toArray)
  match filter with
  | some "throw" => body.set "description" "throw"
  | some "debugger" => body.set "description" "debugger statement"
  | _ => body

/-- Whether the poll channel asks for a pause: its first byte, read through a fresh handle (a
kept one may answer from its buffer), is nonzero. -/
def pollSet (p : System.FilePath) : IO Bool := do
  let b ← (← IO.FS.Handle.mk p .read).read 1
  return b.size > 0 && b[0]! != 0

/-- The poll channel's first byte back to 0. -/
def pollReset : IO Unit := do
  if let some p := (← session.get).poll then
    let h ← IO.FS.Handle.mk p .readWrite
    h.write (ByteArray.mk #[0])
    h.flush

/-- The lines `print` wrote, in `st`. -/
def printedLines (st : State F) (cell : Nat) : Array String :=
  match Debugger.cell? st cell with
  | some (.list xs _) => (Same.seqOf xs).filterMap fun | .str u => some (Show.text u) | _ => none
  | _ => #[]

/-- The `output` event of `lines`, if any. -/
def emitOutput (lines : List String) : IO Unit :=
  if lines.isEmpty then pure ()
  else emit (event · "output" (Json.mk [("category", "stdout"), ("output", String.join (lines.map (· ++ "\n")))]))

/-- A pause: the lines printed since the last, `stopped` with the difference from the previous
pause, then requests until one resumes; the end of the input ends the process. A resume keeps
this pause's state and slots for the next, and clears the poll channel, so that a `pause` served
at the pause does not pause again. -/
def pauseAt (reason : String) (p : Paused) (filter : Option String := none) (hits : List Nat := []) : IO Unit := do
  let fs := p.frames ()
  let p := { p with frames := fun _ => fs }
  let s ← session.get
  let mut printed := s.printed
  if let (some st, some c) := (p.state, s.printCell) then
    let lines := printedLines st c
    emitOutput (lines.toList.drop s.printed)
    printed := lines.size
  let d := match s.prev, p.state with
    | some old, some new => some (diff old new)
    | _, _ => none
  session.modify ({ · with printed, diff := d, changed := changedSlots s.prevSlots fs })
  emit (event · "stopped" (stoppedBody reason p (← session.get) filter hits))
  let some ph' ← serve (.paused p) | IO.Process.exit 0
  let p := match ph' with | .paused p' => p' | _ => p
  let fs := p.frames ()
  session.modify fun s => { s with prev := p.state <|> s.prev, prevSlots := slotsSeen fs, diff := none, changed := [] }
  pollReset

/-- The nonterminals of a dynamic function's whole text and of its body (CreateDynamicFunction,
spec.html:31839, 31835). -/
def fnExprNts : List String := ["FunctionExpression", "GeneratorExpression", "AsyncFunctionExpression", "AsyncGeneratorExpression"]
def fnBodyNts : List String := ["FunctionBody", "GeneratorBody", "AsyncFunctionBody", "AsyncGeneratorBody"]

/-- A dynamic function's parses of its parameters and body (spec.html:31833, 31835), made before the
parse `k` of its whole text (`root`) and of no source yet, with their offsets in that parse's input:
each the newest such parse whose root has the nonterminal and text of `root`'s child of that
nonterminal, at that child's start. -/
def fnParts (n : Names) (roots : List F.Node) (root : F.Node) (k : Nat) (srcs : Sources) : List (Nat × Nat) :=
  let part := fun (below : Nat) (nts : List String) =>
    match (nodeKids root).find? fun c => nts.contains (n.nt (nodeNt c)) with
    | some c => (roots.find? fun r => nodeStamp r < below && !srcs.knows (nodeStamp r) &&
          nodeNt r == nodeNt c && nodeText r == nodeText c).map fun r => (nodeStamp r, (nodeSpan c).1 - (nodeSpan r).1)
    | none => none
  match part k fnBodyNts with
  | some b => b :: (part b.1 ["FormalParameters"]).toList
  | none => []

/-- The covers' reparses (newest first in `covers`) made after the parse `lo` of nodes of a source's
text, of none yet, given that source. -/
def adoptCovers (srcs : Sources) (covers : List (Nat × F.Node)) (lo : Nat) : Sources :=
  (covers.takeWhile (·.1 > lo)).reverse.foldl (init := srcs) fun srcs (c, n) =>
    if srcs.knows c then srcs
    else match srcs.owner.get? (nodeStamp n), srcs.of? (nodeStamp n) with
      | some i, some p => srcs.addOrigin i c (p.origins.getD (nodeStamp n) 0 + (nodeSpan n).1)
      | _, _ => srcs

/-- The parse `k`, seen: a cover's reparse of a source's node is of that source's text; a Script
(not ParseJSON's) is a new source `eval #i`; a dynamic function's whole text a new source
`Function #i`, with its parameters' and body's parses (`fnParts`) and the covers' reparses of their
nodes; a Module whose root spans its text in a bundle's module not yet parsed is that module's; any
other parse is of no source. -/
def Session.noteParse (s : Session) (st : State F) (k : Nat) : Session :=
  if s.srcs.knows k then s
  else match st.roots[k]? with
  | none => s
  | some root => match st.covers.find? (·.1 == k) with
    | some _ => { s with srcs := adoptCovers s.srcs (st.covers.dropWhile (·.1 > k)) (k - 1) }
    | none =>
      let nt := s.names.nt (nodeNt root)
      let mk := fun (name : String) =>
        { path := none, src := nodePoints root, stamp := k, shift := (nodeSpan root).1, root := some root, name,
          ref := k + 1 : Program }
      if nt == "Script" && !st.jsonParses.contains k then
        { s with srcs := s.srcs.add (mk s!"eval #{s.evals + 1}"), evals := s.evals + 1 }
      else if fnExprNts.contains nt then
        let p := mk s!"Function #{s.functions + 1}"
        -- latest first: stamps rise with insertion
        let parts := fnParts s.names st.roots.values.reverse root k s.srcs
        let p := parts.foldl (fun p (j, o) => { p with origins := p.origins.insert j o }) p
        let lo := (parts.map (·.1)).foldl min k
        { s with srcs := adoptCovers (s.srcs.add p) (st.covers.dropWhile (·.1 > k)) lo, functions := s.functions + 1 }
      else if nt == "Module" then
        let (lo, hi) := nodeSpan root
        match s.srcs.all.findIdx? fun p =>
            p.ref ≥ moduleRefBase && p.root.isNone && hi ≤ p.src.size && p.src.extract lo hi == nodePoints root with
        | some i => { s with srcs := s.srcs.adopt i k root }
        | none => s
      else s

/-- The parses made since the hooks last looked (`parses` so far), once armed (`noteParse`). -/
def noteParses (parses : Nat) (st : Option (State F)) : IO Unit := do
  let s ← session.get
  if parses == s.parsesSeen then return
  session.modify ({ · with parsesSeen := parses })
  let some st := st | return
  if !s.armed then return
  let s := (List.range' s.parsesSeen (parses - s.parsesSeen)).foldl (·.noteParse st ·) s
  session.modify ({ · with srcs := s.srcs, evals := s.evals, functions := s.functions })

/-- The program's statement table, once its root Parse Node is in `st`: built, the line
breakpoints resolved, and a `breakpoint` event (`changed`) sent for each. -/
def noteTable (st : Option (State F)) : IO Unit := do
  let s ← session.get
  let (false, some p, some st) := (s.tables.contains 0, s.srcs.program, st) | return
  let some root := st.roots[p.stamp]? | return
  let t := stmtTable s.names p root
  let bs := s.lineBps.map fun b => if b.src == 0 then { b with stmt := resolveLine t b.line b.column } else b
  session.modify ({ · with tables := s.tables.insert 0 t, lineBps := bs, lineAt := bpIndex bs })
  let s ← session.get
  for b in bs.filter (·.src == 0) do
    emit (event · "breakpoint" (Json.mk [("reason", "changed"), ("breakpoint", b.json s)]))

def callerContextSecId : String := "sec-runcallercontext"

/-- Where `tick` said to look: notes the new parses, then pauses where the poll channel asks, at a
breakpoint on the step entered, or as the mode says. Lazy: the depth, the entered step's node, the
execution context stack's length and the frames' nodes, innermost first; `parses`: the parses made
so far. -/
def consider (entered : Option (AlgId × List Nat)) (depth : Unit → Nat) (node : Unit → Option StepNode)
    (contexts : Unit → Nat) (nodes : Unit → List F.Node) (parses : Nat) (paused : Unit → Paused) : IO Unit := do
  noteParses parses (paused ()).state
  if !(← session.get).tables.contains 0 then noteTable (paused ()).state
  let s ← session.get
  if let some p := s.poll then
    if s.pollDue && (← pollSet p) then return ← pauseAt "pause" (paused ())
  let bp := match entered with
    | some (a, p) => match s.bps.get? (a.clause, a.idx) with
      | some ps => ps.contains p
      | none => false
    | none => false
  -- the line breakpoints on the boundary entered
  let hits := if s.lineAt.isEmpty || entered.isNone then []
    else match node () with
      | some nd => if !nd.boundary then [] else match s.srcs.of? nd.stamp with
        | some p => (s.lineAt.getD (p.ref, p.offset nd.stamp nd.lo) []).reverse
        | none => []
      | none => []
  let dbg := match entered with
    | some (a, [1]) => s.debuggerAt.contains (a.clause, a.idx)
    | _ => false
  let boundary := fun (_ : Unit) => entered.isSome && match node () with
    | some nd => nd.boundary && s.srcs.knows nd.stamp
    | none => false
  -- under RunCallerContext, a generator's or async function's context is removed and its caller
  -- not yet resumed: the frames' position is the suspended code's
  let jsPos := fun (_ : Unit) =>
    (nodes ()).any (s.srcs.knows ∘ nodeStamp) &&
      let fs := (paused ()).frames ()
      !((fs.takeWhile fun f => !f.node.any (s.srcs.knows ∘ nodeStamp)).any fun f => s.names.secId f.alg == callerContextSecId)
  let reason? := if bp || !hits.isEmpty then some "breakpoint" else match s.mode with
    | .instr => some s.reason
    | .stepIn => if entered.isSome then some s.reason else none
    | .next d => if entered.isSome && depth () ≤ d then some s.reason else none
    | .out d => if entered.isSome && depth () < d then some s.reason else none
    | .stmtIn => if boundary () then some s.reason else none
    | .stmtNext d =>
      if entered.isNone then none
      else
        let k := contexts ()
        if (k < d && !s.stmtThrow && jsPos ()) || (k ≤ d && boundary ()) then some s.reason else none
    | .stmtOut d =>
      if entered.isNone then none
      else if s.stmtThrow then (if contexts () < d && boundary () then some s.reason else none)
      else if contexts () < d && jsPos () then some s.reason else none
    | .run => none
  match reason? with
  | some reason => pauseAt reason (paused ()) (hits := hits)
  | none =>
    if s.stmtThrow && boundary () then session.modify ({ · with stmtThrow := false })
    if dbg then pauseAt "breakpoint" (paused ()) (some "debugger")

/-- A throw completion's [[Value]]. -/
def thrownValue : Val F → Val F
  | .comp _ x _ => x
  | v => v

/-- The control starts to escape with the throw completion `v` (`raised`: by `?`): pauses with
the `throw` filter, unless the last such pause was at `v` itself, passed on out of a run, or `?`
raises a completion of the same [[Value]], passed on. Each throw made by a step pauses; a
completion made as a value pauses where it is first raised, unless it carries the value of the
last pause. -/
def onThrow (v : Val F) (raised : Bool) (paused : Unit → Paused) : IO Unit := do
  let seen := (← session.get).lastThrow.any fun l =>
    sameObject l v || (raised && sameObject (thrownValue l) (thrownValue v))
  if !seen then
    session.modify ({ · with lastThrow := some v })
    pauseAt "exception" (paused ()) (some "throw")

/-- A run ended in a stop: pauses there with the `stop` filter, once per stop (not again as it
unwinds through the enclosing runs). -/
def onStop (paused : Unit → Paused) : IO Unit := do
  let s ← session.modifyGet fun s => (s, { s with stopShown := true })
  if s.live && s.stopFilter && !s.stopShown then pauseAt "exception" (paused ()) (some "stop")

/-! The root's side. -/

/-- The session on the channel `inp`/`out` (and the poll channel `poll`), with the adapter's
names. -/
def openOn (inp out : IO.FS.Stream) (names : Names) (poll : Option System.FilePath := none) : IO Unit :=
  session.set { inp, out, names, poll }

/-- Requests until the program is launched and configured: the `launch` request, or none when the
input ends first. -/
def awaitLaunch : IO (Option Req) := do
  if (← serve .setup).isSome then return (← session.get).launch else return none

/-- Setup done: the hooks look from here on, the program's Parse Nodes are those of `prog`, the
parses from its on are noted (`noteParses`), and `print` appends to the List cell `printCell`. A
bundle's modules `mods` (`bundlePrograms`) are sources too; each, and a named program, is sent as a
`loadedSource` event. -/
def arm (prog : Option Program := none) (printCell : Option Nat := none) (mods : List Program := [])
    (hostCells : Array Nat := #[8, 9]) : IO Unit := do
  let srcs := mods.foldl Sources.add (Sources.ofProgram prog)
  session.modify ({ · with armed := true, srcs, printCell, hostCells, parsesSeen := (prog.map (·.stamp)).getD 0 })
  for p in (prog.filter (!·.name.isEmpty)).toList ++ mods do
    emit (event · "loadedSource" (Json.mk [("reason", "new"), ("source", p.sourceJson)]))

/-- The run's end: the lines `print` wrote not yet sent (`output`) and the outcome (`terminated`),
then requests until the input ends or `disconnect`. -/
def finish (outcome : String) (code : UInt32) (printed : List String) : IO Unit := do
  let s ← session.modifyGet fun s => (s, { s with armed := false, stopInSetup := false, prev := none })
  emitOutput (printed.drop s.printed)
  emit (event · "terminated" (Json.mk [("outcome", outcome), ("exitCode", .nat code.toNat)]))
  let _ ← serve .ended

end Debugger
