# Interactive JS debugger

A step debugger for the model: a program runs on the specification's machine (`Ecma.Machine`, at the
engine's model), pauses at any step of any spec algorithm, and shows the state the specification
defines. The engine is `ecma-dbg` (`lean/Debugger/Main.lean`), native or as its WebAssembly build
`ecma-dbg-web` in a browser Worker. [DEMO.md](DEMO.md) is the scripted demo: four programs, their
stops and its tests.

## Base: the machine's step interface

The machine (`lean/Ecma/Machine`) runs the specification as data over the observable state
`Ecma.State` (`lean/Ecma/State.lean`):

- `step` makes one transition and returns; the run loop iterates it (`Engine.Machine.runT`). No twin
  of the executor, no shadow state.
- A configuration is the state, the frames (innermost first) and the control. A `Frame` carries its
  algorithm, Parse Node, numbered slots, step path and continuations; so the current step of every
  active algorithm is data.
- With `JS_TRACE_STEPS=1`, ecma-run prints the steps a run enters (`7.3.1 2.a.ii.`).

**The step hook.** The debugger runs the machine's own `step` in a loop (`Debugger.Machine.runW`:
`Engine.Machine.runT` with the trace replaced by an observer) that can pause, through an
`@[implemented_by]` hook and a continuation. A sub-run (a nested spec call) runs under its parent, so a
pause anywhere sees the whole spec stack: the parents' frames (`Parent` holds frames and control, never
the state), then the configuration's. A *step* is a configuration that enters a node or arm (the
`JS_TRACE_STEPS` lines); an *instruction* is one transition.

What the debugger shows is catalogued in [state.md](state.md) (the three layers and the machine's view
of them) and [state-internal.md](state-internal.md) (the spec-internal records and where the model
keeps each).

## Target and build

**wasm64**: Chrome 133+, Firefox 134+, node; no Safari or bun. `scripts/build_wasm.py` (in the flake's
`wasm` shell, README.md) compiles the C that `lake build ecma-dbg` emits with emscripten against the
Lean runtime's wasm64 archives (`nix/lean-wasm`), into `build/web/ecma-dbg-web.{mjs,wasm}`.

## Decided

- **Q1 Engine.** The machine, behind an engine-neutral protocol: the core (`Debugger.*`) never
  reads `Ecma.Gen`, and the machine's adapter (`Debugger.Machine`) fills its names.
- **D6 Parser.** The Lean parser is linked into ecma-dbg-web, so
  `eval`, `Function` and new parses work in the browser; no parse service.
- **D8 Spans.** Each frame's Parse Node is shown with its source excerpt, from the Lean Parse Nodes'
  (lo, hi); statements are stepped as U3 and U4 say.
- **D9 Protocol and UI.** DAP-shaped JSON lines (DAP's envelope and names, `spec*`
  requests and `body.spec` fields), spoken by the engine itself, so that native,
  node and browser hosts are thin transports. The UI is plain ES modules.
- **D10 Serving.** Locally, `tools/dbg/serve.py` (stdlib, 127.0.0.1)
  sends the COOP/COEP/CORP headers SharedArrayBuffer needs. With `--engine` it also runs native ecma-dbg, one
  process a session, for the page (client.mjs's `native-http` transport); the
  Worker build runs in Chrome and Firefox too (`scripts/dbg_browser_test.py`).
- **D11 Dead slots.** Show the slots as the frame holds them; an unbound slot
  reads `unbound`. The machine never clears a slot, so nothing reads "moved" (state.md §4).
- **D12 Spec links.** The pinned step text from the data, with a link to the live
  draft (`tc39.es/ecma262/#sec-…`) marked "live draft; may differ".
- **D13 Pausing.** The engine blocks inside its step hook: in the Worker, a read
  of the command device waits with `Atomics.wait` on a SharedArrayBuffer (needs
  D10's isolation). Replay for step-back can be added on top later.
- **D14 Code placement.** The engine-neutral core is `Debugger.*` (JSON,
  session, protocol, views over `Ecma.State`, names passed in); the machine's adapter and hook are
  `Debugger.Machine`; the root `Debugger.Main` (`ecma-dbg`) runs the machine from
  InitializeHostDefinedRealm's realm, as ecma-run does.
- **D15 Browsers.** Tests run in Chrome (nixpkgs `google-chrome`) and Firefox
  (`firefox-bin-unwrapped`: the pin's source `firefox` builds for aarch64-darwin
  but is not in the binary cache), both unfree and allowed by name with
  `allowUnfreePredicate`; Chromium is Linux-only.
- **U1 Source view.** Hand-written: a `<pre>` per line with a gutter, a
  `<textarea>` to edit, and optional keyword/literal highlighting; no
  CodeMirror or Monaco, so D9 keeps no npm and no build step.
- **U2 Algorithm text.** A `specAlgorithm` {secId, idx} request prints every
  step of the algorithm or SDO row from the data the run executes, errata
  readings nested; the spec.html clause may follow (D12).
- **U3 JS stepping request.** DAP's `granularity: "statement"` on `next`,
  `stepIn` and `stepOut`; without it the unit stays the spec step, so the
  transcripts are unchanged.
- **U4 Stops.** Statements: step 1 of the outermost frame on a statement node
  (not Block, Empty, Labelled, Try or function declarations), plus an arrow's
  expression body. Chrome's finer positions may come later as
  `granularity: "expression"`.
- **U5 Returns.** `stepOut`, and `next` off a function's end, land in the
  caller at the call expression, with the returned value in its slots.
- **U6 JS depth.** The execution context stack's length (O(1)); a built-in's
  context counts, so `next` over `arr.map(f)` skips f and `stepIn` enters it.
- **U7 eval and Function.** Each parse after `arm` is a read-only source
  (`eval #k`, `Function #k`) served by `source` through a `sourceReference`,
  with stepping and line breakpoints, in its own slice (dbg-w4d-eval).
- **U7a Bundles.** A d8 bundle (`// JS_BUNDLE_MODULE...` markers; `--bundle`
  or found in the launch text) runs as ecma-run runs it. Its entry module is the
  program, named by its marker; each other module is a read-only source
  (`sourceReference` 2^30 + i) whose text `source` serves from the start, its
  positions those of its parse once loaded. Each is sent as a `loadedSource`
  event at `arm`; the UI lists them as tabs (line breakpoints in the entry only).
- **U8 UI engine.** Native ecma-dbg behind serve.py by default
  (`serve.py --engine .lake/build/bin/ecma-dbg --page ui/index.html tools/dbg`); the Worker build
  only with `?engine=worker`.
- **U9 Referenced by.** Not built: a reverse index built at a pause on request
  (`specReferrers` {addr}), if the heap pane wants it.

Risks: Memory64 support (Safari); the Emscripten path is unmaintained upstream,
so a Lean bump may need the patches redone; browser Worker stack limits are
untested.
