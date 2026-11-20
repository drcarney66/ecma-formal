# The debugger demo

Four short programs, each stepped through the spec algorithms it runs, on the machine (`ecma-dbg`).
The programs are `tools/dbg/demo/*.js`; their scripts (breakpoints, the stops in order, what each stop
shows and what to say there) are `tools/dbg/demo/script.mjs`, and the tables below follow it. The
tests walk the same scripts and check every stop:

- `scripts/dbg_demo_test.py` (node; native ecma-dbg with `--native`, the WebAssembly build with
  `--wasm-node`): the UI's model, 43 stops and 4 ends (`tools/dbg/demo/demo_test.mjs`).
- `scripts/dbg_browser_test.py --page "ui/index.html?demo"`: the page in headless Chrome or Firefox
  (`tools/dbg/ui/demotest.mjs`), on native ecma-dbg behind serve.py (`--native`) or the WebAssembly
  build (`--web`). It clicks the buttons and reads the panes: status bar, step pane and listing,
  source line and node, spec stack, JS stack, Slots, a slot's cell expanded and shown in the heap pane.

## State

- Native ecma-dbg: `scripts/dbg_demo_test.py --native .lake/build/bin/ecma-dbg` walks all four
  scripts, 47 stops and ends, no failure (2026-11-18); so does the WebAssembly build in node
  (`--wasm-node`).
- The page: `scripts/dbg_browser_test.py --page "ui/index.html?engine=worker&demo"` passes in headless
  Chrome 157 and Firefox 160 (the wasm shell's `chrome` and `firefox`), 47 checks each, and so does
  the site's debugger page (`--site dist --page "debugger/?demo"`, 2026-11-18).
- On the site the four programs are the first group of the examples menu, "The tour", and of the
  Examples page; `debugger/?example=demo/get` opens one.

- Addresses (`#19550`) differ between runs and builds: point at them, do not read them out.

## Setup

1. A checkout, in the dev shell (`nix develop ~/.local/state/ecma-formal/devshell -c bash`).
2. Build the engine:

       lake build ecma-dbg

3. Check the scripts against this build (one ecma-dbg process):

       python3 scripts/dbg_demo_test.py --node node --native .lake/build/bin/ecma-dbg

4. Serve the UI on a fixed port:

       python3 tools/dbg/serve.py --port 8123 --engine .lake/build/bin/ecma-dbg --page ui/index.html tools/dbg

   It prints `serving http://127.0.0.1:8123/ui/index.html?native`. Keep the terminal open: stopping
   it ends the engine.

## Browser

- Chrome or Firefox (both tested), at the URL printed above. A full-screen window: the page has six
  panes (source, console, JS stack, spec stack, step; inspector, heap and state as tabs).
- The status bar's first word is `native`. Each pause reads `paused (REASON) at ALG PATH · depth …`.
- The demo programs are under **tools/dbg/demo** in the examples menu (above the source). Picking one
  replaces the breakpoints and exception filters with its script's, clears "stop on entry" and starts
  it: the first stop below comes by itself.
- Controls: use the buttons. Their keys: continue F8; statement next F10, in F11, out Shift+F11;
  spec step next Alt+F10, in Alt+F11, out Alt+Shift+F11 (on a Mac keyboard, with fn).
- A slot's value with a heap cell has a `#N` link: the link opens the cell in the Heap tab; a click
  on the slot's row expands it in the Inspector. Back with the Inspector tab.

## The programs, in order

Each row: the control that reaches the stop, the stop (status bar, step pane), what to show, what to
say. The first row is the pick. After the last row, **continue** ends the program; the console shows
`terminated: OUTCOME (exit code 0)`.

### 1. get.js: a property get, [[Get]] and OrdinaryGet up the prototype chain

`point.x` is point's own property; `point.z` is found on its prototype. Breakpoint: OrdinaryGet 1.
Ends `normal: 8`.

| # | control | stop | show | say |
|---|---|---|---|---|
| 1 | pick get.js | breakpoint, OrdinaryGet 1, line 3 `a = point.x` | spec stack OrdinaryGet 1 / [[Get]] 1 / GetValue 3.d; JS stack (script), (host); expand obj (x: 3) | `point.x` is a Reference; GetValue 3.d calls point's [[Get]], an ordinary object's, which is OrdinaryGet. obj and receiver are both point. |
| 2 | step next | OrdinaryGet 2 | propertyDesc's cell: Property Descriptor, [[Value]] 3 | [[GetOwnProperty]] found x; step 2 is skipped. |
| 3 | step next | OrdinaryGet 3 | the listing's current step | A data descriptor: OrdinaryGet returns its [[Value]], 3. |
| 4 | continue | breakpoint, OrdinaryGet 1, line 4 `b = point.z` | propertyKey "z" | The same breakpoint for `point.z`; point has no own z. |
| 5 | step next | OrdinaryGet 2 | propertyDesc undefined | Step 2 goes to the prototype. |
| 6 | step next | OrdinaryGet 2.a | | Let parent be obj.[[GetPrototypeOf]](). |
| 7 | step next | OrdinaryGet 2.b | parent's cell (z: 5) | parent is point's [[Prototype]], proto. |
| 8 | step next | OrdinaryGet 2.c | | The lookup recurses, with the same receiver, point. |
| 9 | step in | [[Get]] 1 | obj's cell is proto (z: 5), receiver's point (x: 3) | proto's [[Get]]; obj changed, receiver did not. |
| 10 | step in | breakpoint, OrdinaryGet 1 | spec stack OrdinaryGet 1 / [[Get]] 1 / OrdinaryGet 2.c / [[Get]] 1 | The recursion is on the spec stack; the JS stack is unchanged: no function was called. |
| 11 | step next | OrdinaryGet 2 | propertyDesc [[Value]] 5 | proto's own z. |
| 12 | step next | OrdinaryGet 3 | | 5 returns through both OrdinaryGets; a + b is 8. |

### 2. call.js: a call, EvaluateCall to OrdinaryCallEvaluateBody

`add(2, 3)`. Breakpoints: EvaluateCall 7, OrdinaryCallEvaluateBody 1. Ends `normal: 5`.

| # | control | stop | show | say |
|---|---|---|---|---|
| 1 | pick call.js | breakpoint, EvaluateCall 7, line 5 `add(2, 3)` | func's cell (name "add", length 2), argList's (2, 3), thisValue undefined | EvaluateCall has evaluated the callee and the arguments. |
| 2 | step in | Call 1 | spec stack Call 1 / EvaluateCall 7 | The abstract operation Call. |
| 3 | step next | Call 2 | | IsCallable. |
| 4 | step next | Call 3 | | Call dispatches to the object's own [[Call]]. |
| 5 | step in | [[Call]] 1 | callerContext, result unbound | An ECMAScript function object's [[Call]]; step 2 pushes a new execution context. |
| 6 | continue | breakpoint, OrdinaryCallEvaluateBody 1 | JS stack add, (script), (host); spec stack … [[Call]] 6 | add's execution context is on the JS stack now. |
| 7 | in (statement) | line 2 `var s = a + b;` | | Statement stepping: add's first statement. |
| 8 | next (statement) | line 3 `return s;` | | |
| 9 | out (statement) | [[Call]] 8, line 5 | result `Completion { type: ~return~, value: 5, … }`; JS stack (script), (host) | Step 7 popped add's context; a return completion, whose [[Value]] step 10 returns. |

### 3. forof.js: a for-of loop, the iterator protocol

`for (const v of [10, 20])`. Breakpoint: ForIn/OfBodyEvaluation 8.a (the Repeat step's call of
next). Ends `normal: 30`.

| # | control | stop | show | say |
|---|---|---|---|---|
| 1 | pick forof.js | breakpoint, ForIn/OfBodyEvaluation 8.a, line 2 | iteratorRecord's cell: Iterator Record, [[NextMethod]], [[Done]] false | The Repeat step: call next on the array iterator. |
| 2 | step next | 8.b | nextResult's cell: value 10, done false | An iterator result object. |
| 3 | step next | 8.c | | |
| 4 | step next | 8.d | | IteratorComplete. |
| 5 | step in | IteratorComplete 1 | | It reads the result's `done` through [[Get]]. |
| 6 | step out | 8.e | done false | The loop goes on. |
| 7 | step next | 8.f | | IteratorValue. |
| 8 | step next | 8.g | nextValue 10 | v is bound to 10 in a new environment. |
| 9 | next (statement) | line 3 `sum = sum + v;` | spec stack … ForIn/OfBodyEvaluation 8.j | The body, evaluated from 8.j. |
| 10 | continue | breakpoint, 8.a | iterationResult 10 | The second iteration. |
| 11 | continue | breakpoint, 8.a | iterationResult 30; nextResult still value 20 | The third call of next. |
| 12 | step next | 8.b | nextResult: value undefined, done true | The iterator is exhausted. |
| 13 | step next | 8.c | | |
| 14 | step next | 8.d | | |
| 15 | step next | 8.e | done true | The loop returns iterationResult, 30. |
| 16 | step next | Completion 1 | completionRecord `Completion { type: ~normal~, value: 30, … }` | The loop's result as a completion record. |

### 4. throw.js: a throw, completion records up to the catch clause

`check(-1)` throws a RangeError, caught by the caller. The exception filter "throw" and a breakpoint
at CatchClauseEvaluation 1. Ends `normal: "negative"`.

| # | control | stop | show | say |
|---|---|---|---|---|
| 1 | pick throw.js | exception, Evaluation 3 "Throw exprValue.", line 2 | JS stack check, (script), (host); exprValue's cell (message "negative") | The throw filter stops at ThrowStatement's Evaluation, inside check. |
| 2 | step next | Completion 1 | completionRecord `Completion { type: ~throw~, value: #N, … }` | A throw is a completion record; each algorithm passes it on. |
| 3 | step out | Evaluation 5 (the if statement's) | stmtCompletion the throw completion | Its `?` returns the completion to its caller. |
| 4 | out (statement) | breakpoint, CatchClauseEvaluation 1, line 8 | thrownValue's cell (message "negative"); JS stack (script), (host) | The completion went up through check's body and [[Call]] to the try statement; check's context is gone. |
| 5 | next (statement) | line 9 `msg = e.message;` | spec stack … CatchClauseEvaluation 7 | The catch block, e bound to the error. |
| 6 | next (statement) | line 11 `msg;` | | After the try statement. |

## If a step fails

- **A stop is not the table's:** ↻ restart (the same breakpoints) and redo the rows; or pick the
  program again from the examples. Each program's key stops are breakpoints, so **continue** gets
  back on the script: get.js rows 4 and 10, call.js row 6, forof.js rows 10 and 11, throw.js row 4.
- **A pane is empty or loading:** select the spec stack's top frame, or the Inspector tab.
- **The status bar says `no session` or the console `engine trap`:** the engine ended. Pick the
  program again; if that fails, stop serve.py (Ctrl-C) and run it again, then reload the page.
- **Nothing works in the browser:** show the same stops in the terminal, what each shows as one JSON
  line:

      python3 scripts/dbg_demo_test.py --node node --native .lake/build/bin/ecma-dbg --dump get.js

## The spec issues' examples

Every program of `docs/spec-issues/examples/` is an example of the UI, under
**docs/spec-issues** in the examples menu, named by its report's number and title (`01
Number::multiply gives +0 for +0 × -5`). `scripts/build_site.py` makes the list
(`build/spec-examples.json`, by `scripts/dbg_spec_examples.py`), checks it on native ecma-dbg and on the
WebAssembly build in node, and puts it on the site, where each write-up's page links its example:

- A `.js` file is a Script, as RESULTS.md runs it. A directory (02, 04, 15: `main.mjs` and its
  modules) is the d8 bundle `ecma-bundle` writes of it at build time, `main.mjs` the entrypoint; the
  debugger shows each module as a tab. Nothing bundled is committed.
- Each runs with the options RESULTS.md's model run has: none (ecma-run's default host). The list's
  `args`, sent as `launch`'s, would carry others.
- Where the report's Location line names a clause and step (`(#sec-id), step S`, its first), picking
  the example sets a breakpoint there and stops on entry: **continue** lands on the step.
  13's is the second step its line names (1.i). No breakpoint where the model's run does not reach
  the step or the line names none (`NO_BREAKPOINT` in the script): 05, 06 (the default host's agent
  cannot block, so DoWait throws at step 12), 14 (toString returns at step
  2), 33 (CreateIntrinsics runs in the realm's setup, before the entry), and 26, 29, 32, 35,
  39-41 and 44, whose reports name grammar or early-error rules.
- Where the model's run ends at an erratum's or an Assert's stop at a step (02, 08, 10, 11, 34), the
  `stop` filter is on too: **continue** pauses at that stop, then ends.
- 46 is listed, not run: its run does not end within RESULTS.md's 120 s natively, and the Worker
  build is slower. Picking it shows its source and the reason.
- Its end is the model's run: RESULTS.md's for a Script; for a directory, `ecma-run --module
  --module-dir DIR DIR/main.mjs`, run at build time (RESULTS.md has no model run of a Module).

A link opens one directly, by its id, the example's file name without `.js` or its directory's
name:

    ui/?engine=worker&example=01-number-multiply-zero-sign
    ui/?engine=worker&example=02-gather-available-ancestors

(`ui/index.html?...` the same; on the site, `/debugger/?example=ID`.) An
unknown id says so in the console; an example the Worker build cannot run is shown with its reason
and not started.

Tests:

- `scripts/dbg_browser_test.py --site DIST --page "debugger/?examples"`: the site in headless Chrome (`tools/dbg/ui/spectest.mjs`): each runnable example picked, stopped on entry,
  continued to its breakpoint, then to its end, checked against the model's run (the result line, a
  `?` step any; the exit code; the printed lines).
- `scripts/dbg_demo_test.py --json build/spec-examples.json` (native ecma-dbg, or the WebAssembly
  build in node): the same on the UI's model, `tools/dbg/ui/spec_examples_test.mjs`.
- `scripts/dbg_spec_bundles_test.py`: each generated bundle runs on the model (`ecma-run --bundle`)
  as its directory does, and as the example's expected end.
