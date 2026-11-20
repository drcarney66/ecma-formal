module

public import Debugger.Json

@[expose] public section

/-!
# The debugger's protocol: the envelope

DAP-shaped JSON lines (docs/debugger/README.md, D9). The client sends requests
`{"seq", "type": "request", "command", "arguments"}`; the engine answers each with a response
`{"seq", "type": "response", "request_seq", "command", "success", "body"}` (`message` on failure)
and sends events `{"seq", "type": "event", "event", "body"}`.

Sources: the program, and each eval or Function parse made after `arm` (`Debugger.Session.noteParse`):
a Script's is `eval #k`, a dynamic function's whole text `Function #k` (its parameters' and body's
parses, which run, mapped into it), each with `sourceReference` its parse's stamp + 1 and its root
node's text as its text. A source in a frame or `js` is {name, path} for the program, {name,
sourceReference} for the others.

Requests (`Debugger.Session` serves them):
- `initialize` → the capabilities, then the event `initialized`;
- `launch` {program (a path) or source, args (ecma-run's options), stopOnEntry, stopInSetup};
- `setSpecBreakpoints` {breakpoints: [{alg, path?}]}, `alg` a sec-id, `sec-id#idx` or an
  algorithm's name, `path` a step path (`2.a.ii`), else the algorithm's first step; the reply
  lists each breakpoint `verified` with the algorithms it resolved to;
- `setBreakpoints` {source: {path} or {sourceReference}, breakpoints: [{line, column?}]}: the source's
  line breakpoints replaced (one made by the run's parse once that parse exists), each with a new id, resolved to the first statement boundary on that line (at or after
  `column`, if given), else on the next line that has one; before the program's statement table
  (its root Parse Node in `State.roots`) each is `verified: false`, message "pending", and a
  `breakpoint` event resolves it once the table is built;
- `breakpointLocations` {source, line, endLine?}: the statement boundaries' lines and columns on
  those lines; before the statement table, an error "pending";
- `setExceptionBreakpoints` {filters}: `stop` pauses at a model stop, `throw` where a throw
  completion starts to escape, `debugger` at a `debugger` statement (its Evaluation, step 1);
- `configurationDone`: the run starts once it and `launch` are in;
- `continue`, `next`, `stepIn` (`granularity: "instruction"`: one transition), `stepOut`; with
  `granularity: "statement"` the unit is the JS statement, the depth the execution context stack's
  length d: `stepIn` pauses at the next statement boundary (step 1 of the outermost frame on a
  statement node), `next` at the next one at most d deep or the first JS-positioned step less deep
  (a return lands at the call), `stepOut` at that step; after a throw escapes, at a boundary only;
- `pause`: requests are read only at a pause, so while the run goes on the client also sets the
  poll channel (`--dbg-poll`, `Debugger.Session`); the run pauses (`stopped`, reason `pause`) and then
  answers it;
- `threads` (one, "agent"), `disconnect`;
- `source` {sourceReference} or {source}, at any phase: the source's {content, mimeType};
- `specAlgorithm` {secId, idx}, {secId} or {alg} (as a breakpoint's, naming one algorithm), at any phase: its
  listing {name, secId, idx, kind (alg | row), production? (an SDO row's, as written), params, steps},
  each step {path, text, depth, reading?, steps?} as a frame shows it, in order, its sub-steps
  nested: an `If`'s arms after it, a closure's steps under the step evaluating its literal, an
  erratum's readings under its step, numbered within the reading (`reading`, its overlay id);
- at a pause: `stackTrace` (frames with `source`, `line`, `column`, `endLine`, `endColumn`, `lo` and
  `hi` where the frame's Parse Node is of a source's text, in code points in it; `spec` {secId, idx, path, text, kind, run, flags?, node?}): the
  whole spec stack, a suspended generator's or async caller's saved frames too, so `totalFrames` can
  exceed `stopped`'s `spec.depth`, the running computation's frames, which stepping compares; `scopes` {frameId}
  (Slots, Step, Node, Execution contexts) and `variables` {variablesReference, start?, count?}: a
  scope's, or a heap cell's (its address + 1) parts by its kind, a List's paged by `start` and
  `count` (`Debugger.View`, `Debugger.Heap`); a part that differs from the previous pause's has
  `presentationHint.attributes` ["changed"], a List `indexedVariables`;
- at a pause: `stackTrace {view: "js"}` {startFrame?, levels?}: one frame for each execution
  context, the running one first, each {id, name, its JS position as a frame's (line 0 without one),
  inBuiltin?, spec {frames {lo, hi}, site?}} (`Debugger.JSStack`), with `totalFrames` and `contexts`,
  the stack's length;
- at a pause: `specHeap` {from, count?, kind? (record | list | object | env)}: the cells of
  `[from, from + count)`, each {addr, kind, type, summary, variablesReference}, and `heapSize`;
  `specState`: the Agent Record, the Symbols and parses so far, each parse's root, the running
  SDOs' Parse Nodes, the arguments Lists passed, and `host` {transitions, steps, hostLog,
  shapeLog}; `specDiff` {addr}: the cell at the previous pause (`old`, null if new since) and now
  (`new`), each {kind, summary, variables}, and the names of the parts that changed.

Events: `initialized`; `stopped` {reason: entry | step | breakpoint | exception | pause,
description? (throw, debugger statement), hitBreakpointIds? (the line breakpoints on the boundary), spec: {alg, secId, idx, path, reading?, text, depth, steps, transitions,
stop?, filter?, diff?}, js: {source, line, column, endLine, endColumn, lo, hi, statement?, inBuiltin?,
contexts}}, `diff` from the second pause on {newCells: [lo, hi), changed: at most 50
addresses of earlier cells that differ, truncated, stackChanged}; `js` is the innermost frame's node
of a source's text (lo, hi: code points in it), `statement` {lo, hi, line, column, endLine, endColumn}
the innermost statement node's, `inBuiltin`, where that frame has no JS node and a built-in
function runs, its algorithm (the frame inside the innermost BuiltinCallOrConstruct), `contexts` the execution context stack's length (alone where no frame has a JS node); `output` {category: stdout,
output: the lines `print` wrote since the last pause, sent before `stopped` or `terminated`};
`breakpoint` {reason: changed, breakpoint: {id, verified, line, column?, source?, message?}}, a
pending line breakpoint resolved; `terminated` {outcome: ecma-run's result line, exitCode}.
-/

namespace Debugger

/-- A request: its sequence number, command and arguments (`{}` when absent). -/
structure Req where
  seq : Nat
  command : String
  args : Json

/-- A request from its JSON. -/
def Req.ofJson (j : Json) : Except String Req := do
  let some "request" := (j.get? "type").bind Json.str? | throw "not a request"
  let some command := (j.get? "command").bind Json.str? | throw "a request without a command"
  return { seq := ((j.get? "seq").bind Json.nat?).getD 0, command, args := (j.get? "arguments").getD (.obj #[]) }

/-- The response to `r`, numbered `seq`. -/
def response (seq : Nat) (r : Req) (body : Json := .obj #[]) : Json :=
  Json.mk [("seq", .nat seq), ("type", "response"), ("request_seq", .nat r.seq), ("command", r.command),
    ("success", true), ("body", body)]

/-- A failed response to `r`. -/
def errorResponse (seq : Nat) (r : Req) (msg : String) : Json :=
  Json.mk [("seq", .nat seq), ("type", "response"), ("request_seq", .nat r.seq), ("command", r.command),
    ("success", false), ("message", msg)]

/-- The event `name`, numbered `seq`. -/
def event (seq : Nat) (name : String) (body : Json := .obj #[]) : Json :=
  Json.mk [("seq", .nat seq), ("type", "event"), ("event", name), ("body", body)]

/-- The exception filters: `stop`, a model stop (residue, an assert, …); `throw`, a
throw completion starting to escape, not again as it is passed on; `debugger`, a `debugger`
statement. -/
def exceptionFilters : Json :=
  .arr #[Json.mk [("filter", "stop"), ("label", "Model stop"), ("default", false)],
    Json.mk [("filter", "throw"), ("label", "Throw completion"), ("default", false)],
    Json.mk [("filter", "debugger"), ("label", "debugger statement"), ("default", false)]]

/-- The reply to `initialize`. -/
def capabilities : Json :=
  Json.mk [("supportsConfigurationDoneRequest", true), ("supportsSteppingGranularity", true),
    ("supportsSpecBreakpoints", true), ("supportsBreakpointLocationsRequest", true),
    ("exceptionBreakpointFilters", exceptionFilters)]

/-- The one thread. -/
def threads : Json := Json.mk [("threads", .arr #[Json.mk [("id", 1), ("name", "agent")]])]

/-- A field of a request's arguments. -/
def Req.arg? (r : Req) (k : String) : Option Json := r.args.get? k

def Req.flag (r : Req) (k : String) : Bool := ((r.arg? k).bind Json.bool?).getD false

end Debugger
