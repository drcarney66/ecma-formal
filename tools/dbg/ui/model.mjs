// The debugger UI's model, with no DOM: a session of tools/dbg/client.mjs, the
// configuration (program, spec breakpoints, line breakpoints by program name, exception
// filters, stopOnEntry) and the snapshot of the current pause. The panes listen to its
// changes:
//
//   const m = new Model(client, { program: {name, source, args?}, breakpoints: [{alg, path}],
//                                 lineBreakpoints: {"a.js": [{line, column?}]}, buildArgs: [...] });
//   m.on("change", (what) => ...);   // state, pause, frames, jsFrames, select, scopes,
//                                    // vars, output, breakpoints, filters, program,
//                                    // heap, openState, span, locations, listing, sources
//   m.start();                       // a new session on the configuration
//   m.stepIn(); await m.until((m) => m.state === "paused");
//
// At a pause it asks, pipelined, for `stackTrace` (FRAME_PAGE levels), the JS stack
// (`stackTrace {view: "js"}`, all of it), the selected frame's `scopes` and its Slots;
// the rest loads on demand (`moreFrames`, `selectFrame`, `selectJsFrame`, `variables`,
// `spec`: specHeap, specState, specDiff). Responses of an
// earlier pause are dropped. `listing` asks for an algorithm's `specAlgorithm`, kept
// for the model's life (it depends only on the engine's data). `openHeap` and `selectSpan` ask the heap and source panes
// to show a cell or a span. A breakpoint or filter changed while the run goes on is
// sent at a pause the model asks for and does not show: `pause`, the set, then
// `continue`. A line breakpoint's status is setBreakpoints' reply, then its `breakpoint`
// events (pending until the engine has the program's statement table); the breakable
// lines (`locations`) are asked for at each pause until the engine has them. The eval and
// Function code the run parses are sources of their own (a `sourceReference`): one opens,
// its text asked for by `source`, when a pause's position or a selected JS frame's is first
// in it, and the source shown (`sourceShown`, 0 the program) follows those positions. A
// bundle's modules arrive as `loadedSource` events at the start: the entry module is the
// program (`program`: its name and text), each other one opens as a source.

export const FRAME_PAGE = 50;
export const LIST_PAGE = 100;
// The variablesReference values below this are heap cells, at their address + 1
// (Dbg.scopeBase); scopes are above.
export const SCOPE_BASE = 2 ** 44;

// The heap address of the cell `v` expands to, or null.
export function cellOf(v) {
  const r = v?.variablesReference ?? 0;
  return r > 0 && r < SCOPE_BASE ? r - 1 : null;
}

// A position's source: its `sourceReference`, 0 for the program.
export function sourceRef(source) {
  return source?.sourceReference ?? 0;
}

// The exception filters before a session's `initialize` lists them.
export const FILTERS = [
  { filter: "stop", label: "Model stop" },
  { filter: "throw", label: "Throw completion" },
  { filter: "debugger", label: "debugger statement" },
];

export class Model {
  constructor(client, config = {}) {
    this.client = client;
    this.config = { program: null, breakpoints: [], lineBreakpoints: {}, filters: [], stopOnEntry: false, buildArgs: [], ...config };
    this.listeners = [];
    this.session = null;
    // idle | setup | running | paused | terminated | ended
    this.state = "idle";
    this.program = null;
    this.capabilities = null;
    this.bpStatus = [];
    this.lineStatus = [];
    this.lineChanged = new Map();
    this.locations = null;
    this.locating = null;
    this.filterStatus = [];
    this.snap = null;
    this.gen = 0;
    this.output = [];
    this.ending = null;
    this.quiet = null;
    this.chain = Promise.resolve();
    this.heapAsk = null;
    this.span = null;
    // secId#idx: the listing, null if refused, or the pending request
    this.listings = new Map();
    // the session's sources by sourceReference: {ref, name, text (null while it loads),
    // module (a bundle's)}
    this.sources = new Map();
    this.sourceShown = 0;
  }

  on(name, fn) {
    if (name === "change") this.listeners.push(fn);
    return this;
  }

  emit(what) {
    for (const fn of this.listeners) fn(what);
  }

  // Resolves once `pred(this)` holds (checked at each change), or rejects after `ms`.
  until(pred, ms = 60000) {
    if (pred(this)) return Promise.resolve(this);
    return new Promise((res, rej) => {
      const t = setTimeout(() => {
        this.listeners.splice(this.listeners.indexOf(check), 1);
        rej(new Error(`timed out in state ${this.state}`));
      }, ms);
      const check = () => {
        if (!pred(this)) return;
        clearTimeout(t);
        this.listeners.splice(this.listeners.indexOf(check), 1);
        res(this);
      };
      this.listeners.push(check);
    });
  }

  setState(state) {
    this.state = state;
    this.emit("state");
  }

  log(category, text) {
    this.output.push({ category, text });
    this.emit("output");
  }

  // The filters the engine offers: initialize's, else FILTERS.
  filters() {
    return this.capabilities?.exceptionBreakpointFilters ?? FILTERS;
  }

  setProgram(program) {
    this.config.program = program;
    this.emit("program");
  }

  // A new session on the configuration; the old one, if any, ends.
  start() {
    this.end();
    this.state = "setup";
    const s = this.client.session(this.config.program);
    this.session = s;
    this.program = this.config.program;
    this.output = [];
    this.ending = null;
    this.snap = null;
    this.quiet = null;
    this.chain = Promise.resolve();
    this.span = null;
    this.lineStatus = [];
    this.lineChanged = new Map();
    this.locations = null;
    this.locating = null;
    this.sources = new Map();
    this.sourceShown = 0;
    this.gen++;
    this.emit("output");
    this.emit("sources");
    s.on("message", (m) => s === this.session && this.message(s, m));
    s.on("stderr", (l) => s === this.session && this.log("stderr", l));
    s.on("exit", (c) => s === this.session && this.exited(`exit ${c}`));
    s.on("trap", (t) => s === this.session && this.exited(`engine trap: ${t}`));
    this.setState("setup");
    this.emit("pause");
    s.request("initialize", { adapterID: "ecma-dbg" }).then((r) => {
      if (s !== this.session || !r?.success) return;
      this.capabilities = r.body;
      this.emit("filters");
    });
    // The build's arguments (`buildArgs`, builds.mjs), then the program's own.
    const args = [...(this.config.buildArgs ?? []), ...(this.config.program?.args ?? [])];
    s.request("launch", { program: s.program, stopOnEntry: this.config.stopOnEntry, ...(args.length ? { args } : {}) });
    this.sendBreakpoints(s);
    this.sendLineBreakpoints(s);
    this.sendFilters(s);
    s.request("configurationDone");
    this.setState("running");
  }

  restart() {
    this.start();
  }

  // Ends the session: the engine is killed.
  stop() {
    if (!this.session) return;
    this.end();
    this.snap = null;
    this.log("exit", "stopped");
    this.setState("ended");
  }

  end() {
    const s = this.session;
    if (!s) return;
    this.session = null;
    s.terminate();
  }

  exited(line) {
    this.log("exit", line);
    this.session = null;
    if (this.state !== "terminated") {
      this.snap = null;
      this.setState("ended");
    }
  }

  // An engine message: the state moves on events, which arrive in order (a response's
  // promise settles later, in a microtask).
  message(s, m) {
    if (m.type !== "event") return;
    if (m.event === "stopped") this.stopped(s, m.body);
    else if (m.event === "output") this.log(m.body.category ?? "stdout", m.body.output);
    else if (m.event === "breakpoint") this.lineBreakpointChanged(m.body.breakpoint);
    else if (m.event === "loadedSource") this.loadedSource(s, m.body.source);
    else if (m.event === "terminated") {
      this.ending = m.body;
      this.snap = null;
      this.log("terminated", `terminated: ${m.body.outcome} (exit code ${m.body.exitCode})`);
      this.setState("terminated");
      s.request("disconnect");
    }
  }

  stopped(s, body) {
    if (this.quiet) {
      this.quiet.held = body;
      return;
    }
    this.show(s, body);
  }

  // A new pause: the snapshot, then stackTrace, scopes and the Slots, pipelined.
  show(s, body) {
    const gen = ++this.gen;
    this.snap = {
      gen, stopped: body, frames: [], totalFrames: null, selected: 0, jsFrames: null, jsSelected: null,
      scopes: new Map(), vars: new Map(), spec: new Map(),
    };
    this.span = null;
    this.state = "paused";
    if (body.js?.line > 0) this.openSource(s, body.js.source);
    this.emit("pause");
    this.emit("state");
    this.loadFrames(s, gen, 0);
    this.loadJsFrames(s, gen);
    this.loadScopes(s, gen, 0);
    if (!this.locations) this.loadLocations(s);
  }

  // Shows the source of a position (`source` as a frame has it), opening it if it is
  // code the run parsed and not yet open; `show` false: only opens it.
  openSource(s, source, show = true, module = false) {
    const ref = sourceRef(source);
    if (ref && !this.sources.has(ref)) {
      this.sources.set(ref, { ref, name: source.name ?? `source ${ref}`, text: null, module });
      s.request("source", { sourceReference: ref }).then((r) => {
        const src = this.sources.get(ref);
        if (s !== this.session || !src) return;
        src.text = r?.success ? r.body.content : "";
        this.emit("sources");
      });
    }
    if (show) this.showSource(ref);
  }

  // A `loadedSource` event, a bundle's module: the entry module (sourceReference 0)
  // becomes the program, by its name and text; another opens as a source.
  loadedSource(s, source) {
    const ref = sourceRef(source);
    if (ref) return this.openSource(s, source, false, true);
    s.request("source", { sourceReference: 0 }).then((r) => {
      if (s !== this.session || !r?.success) return;
      this.program = { name: source.name, source: r.body.content };
      this.emit("sources");
    });
  }

  // Shows the source `ref` (0: the program), if open.
  showSource(ref) {
    if (ref && !this.sources.has(ref)) return;
    this.sourceShown = ref;
    this.emit("sources");
  }

  // The program's breakable lines, once the engine has its statement table.
  loadLocations(s) {
    if (this.locating === s) return;
    this.locating = s;
    s.request("breakpointLocations", { source: { path: s.program }, line: 1, endLine: 2 ** 31 }).then((r) => {
      if (s !== this.session) return;
      this.locating = null;
      if (!r?.success) return;
      this.locations = new Set(r.body.breakpoints.map((b) => b.line));
      this.emit("locations");
    });
  }

  current(s, gen) {
    return s === this.session && this.snap?.gen === gen ? this.snap : null;
  }

  loadFrames(s, gen, startFrame, levels = FRAME_PAGE) {
    return s.request("stackTrace", { threadId: 1, startFrame, levels }).then((r) => {
      const snap = this.current(s, gen);
      if (!snap || !r?.success) return;
      snap.frames.splice(startFrame, Infinity, ...r.body.stackFrames);
      snap.totalFrames = r.body.totalFrames;
      this.emit("frames");
    });
  }

  loadJsFrames(s, gen) {
    return s.request("stackTrace", { threadId: 1, view: "js" }).then((r) => {
      const snap = this.current(s, gen);
      if (!snap || !r?.success) return;
      snap.jsFrames = r.body.stackFrames;
      this.emit("jsFrames");
    });
  }

  loadScopes(s, gen, frameId) {
    return s.request("scopes", { frameId }).then((r) => {
      const snap = this.current(s, gen);
      if (!snap || !r?.success) return;
      snap.scopes.set(frameId, r.body.scopes);
      this.emit("scopes");
      const slots = r.body.scopes.find((x) => x.name === "Slots");
      if (slots) this.variables(slots.variablesReference);
    });
  }

  // The next FRAME_PAGE frames.
  moreFrames() {
    const snap = this.snap;
    if (this.state !== "paused" || !snap || snap.totalFrames === null || snap.frames.length >= snap.totalFrames) return null;
    return this.loadFrames(this.session, snap.gen, snap.frames.length);
  }

  // Selects spec frame `i`; a JS frame selected (`js`) shows its position in the source.
  selectFrame(i, js = null) {
    const snap = this.snap;
    if (!snap || (i === snap.selected && js === snap.jsSelected)) return;
    snap.selected = i;
    const moved = js !== snap.jsSelected;
    snap.jsSelected = js;
    if (moved && this.session) {
      const f = js === null ? snap.stopped.js : snap.jsFrames?.[js];
      if (f?.line > 0) this.openSource(this.session, f.source);
    }
    this.emit("select");
    if (!snap.scopes.has(i) && this.state === "paused") this.loadScopes(this.session, snap.gen, i);
  }

  // Selects JS frame `j` and its innermost spec frame, loading the spec frames up to it.
  async selectJsFrame(j) {
    const snap = this.snap;
    const f = snap?.jsFrames?.[j];
    if (!f) return;
    const lo = f.spec.frames.lo;
    if (lo >= snap.frames.length && this.state === "paused") {
      await this.loadFrames(this.session, snap.gen, snap.frames.length, lo + FRAME_PAGE - snap.frames.length);
    }
    if (this.snap === snap) this.selectFrame(lo, j);
  }

  frame() {
    return this.snap?.frames[this.snap.selected] ?? null;
  }

  // The innermost loaded frame with a JS position (`line > 0`), or null.
  jsFrame() {
    return this.snap?.frames.find((f) => f.line > 0) ?? null;
  }

  // The JS frame whose spec frames hold spec frame `i`, or null.
  jsFrameOf(i) {
    return this.snap?.jsFrames?.find((f) => f.spec.frames.lo <= i && i < f.spec.frames.hi) ?? null;
  }

  // The position the source shows: the selected JS frame's, else the innermost spec
  // frame's with one; {line, lo, hi, ref} in code points in the source `ref`, or null.
  jsPosition() {
    const snap = this.snap;
    if (!snap) return null;
    if (snap.jsSelected !== null) {
      const f = snap.jsFrames?.[snap.jsSelected];
      return f && f.line > 0 ? { line: f.line, lo: f.lo, hi: f.hi, ref: sourceRef(f.source) } : null;
    }
    const f = this.jsFrame();
    return f ? { line: f.line, lo: f.lo ?? f.spec.node?.lo ?? 0, hi: f.hi ?? f.spec.node?.hi ?? 0, ref: sourceRef(f.source) } : null;
  }

  varKey(ref, start, count) {
    return start === undefined ? `${ref}` : `${ref}:${start}:${count}`;
  }

  // The variables of `ref` at this pause (`start`/`count`: a page of a List's), cached:
  // a promise of the list, null if the pause is over first.
  variables(ref, start, count) {
    const snap = this.snap;
    if (!snap) return Promise.resolve(null);
    const key = this.varKey(ref, start, count);
    const have = snap.vars.get(key);
    if (have) return Array.isArray(have) ? Promise.resolve(have) : have;
    if (this.state !== "paused") return Promise.resolve(null);
    const s = this.session;
    const args = { variablesReference: ref };
    if (start !== undefined) Object.assign(args, { filter: "indexed", start, count });
    const p = s.request("variables", args).then((r) => {
      if (!this.current(s, snap.gen)) return null;
      const vs = r?.success ? r.body.variables : [{ name: "error", value: r?.message ?? "no answer", type: "", variablesReference: 0 }];
      snap.vars.set(key, vs);
      this.emit("vars");
      return vs;
    });
    snap.vars.set(key, p);
    return p;
  }

  // The variables of `ref` already loaded, or undefined.
  loaded(ref, start, count) {
    const v = this.snap?.vars.get(this.varKey(ref, start, count));
    return Array.isArray(v) ? v : undefined;
  }

  // A spec request at this pause (specHeap, specState, specDiff), cached by its
  // arguments: a promise of its body, null if it fails or the pause is over first.
  spec(command, args = {}) {
    const snap = this.snap;
    if (!snap) return Promise.resolve(null);
    const key = `${command} ${JSON.stringify(args)}`;
    const have = snap.spec.get(key);
    if (have) return have;
    if (this.state !== "paused") return Promise.resolve(null);
    const s = this.session;
    const p = s.request(command, args).then((r) => (this.current(s, snap.gen) && r?.success ? r.body : null));
    snap.spec.set(key, p);
    return p;
  }

  // The listing of algorithm or SDO row secId#idx (`specAlgorithm`): the listing, null
  // if the engine refused it, or undefined while it loads (a "listing" change follows).
  listing(secId, idx) {
    const key = `${secId}#${idx}`;
    const have = this.listings.get(key);
    if (have !== undefined && !(have instanceof Promise)) return have;
    if (!have && this.session) {
      const p = this.session.request("specAlgorithm", { secId, idx }).then((r) => {
        if (r) this.listings.set(key, r.success ? r.body : null);
        else this.listings.delete(key);
        this.emit("listing");
      });
      this.listings.set(key, p);
    }
    return undefined;
  }

  // Toggles a spec breakpoint at step `path` of secId#idx: off if one is there (by
  // that algorithm or one its `alg` resolved to), else on as {alg: "secId#idx", path}.
  toggleBreakpoint(secId, idx, path) {
    const key = `${secId}#${idx}`;
    const bps = this.config.breakpoints;
    const at = bps.map((bp, i) => this.breakpointAt(bp, this.bpStatus[i], secId, idx) && (bp.path ?? "1") === path);
    return this.setBreakpoints(at.includes(true) ? bps.filter((_, i) => !at[i]) : [...bps, { alg: key, path }]);
  }

  // Whether breakpoint `bp` (with the engine's `status`, if any) is in secId#idx.
  breakpointAt(bp, status, secId, idx) {
    const key = `${secId}#${idx}`;
    return bp.alg === key || (idx === 0 && bp.alg === secId) || (status?.resolved ?? []).includes(key);
  }

  // `specHeap`: the cells of [from, from + count), of `kind` if given.
  heap(from, count, kind) {
    return this.spec("specHeap", kind ? { from, count, kind } : { from, count });
  }

  // The pause's `stopped.spec.diff`, or null (the first pause, or not paused).
  diff() {
    return (this.state === "paused" && this.snap?.stopped.spec?.diff) || null;
  }

  // Asks the heap pane to show `view`: {addr} a cell, {mode: "new"} the new cells,
  // {mode: "changed"} the changed ones.
  openHeap(view) {
    this.heapAsk = view;
    this.emit("heap");
  }

  // Asks for the state pane (the execution contexts).
  openState() {
    this.emit("openState");
  }

  // Asks the source pane to select code points [lo, hi) of the program.
  selectSpan(lo, hi) {
    this.span = { lo, hi };
    this.showSource(0);
    this.emit("span");
  }

  resume(command, args = {}) {
    if (this.state !== "paused") return false;
    this.snap = null;
    this.setState("running");
    this.session.request(command, { threadId: 1, ...args });
    return true;
  }

  cont() {
    return this.resume("continue");
  }

  next() {
    return this.resume("next");
  }

  stepIn() {
    return this.resume("stepIn");
  }

  stepOut() {
    return this.resume("stepOut");
  }

  stepInstruction() {
    return this.resume("stepIn", { granularity: "instruction" });
  }

  // Statement stepping (`granularity: "statement"`).
  jsNext() {
    return this.resume("next", { granularity: "statement" });
  }

  jsIn() {
    return this.resume("stepIn", { granularity: "statement" });
  }

  jsOut() {
    return this.resume("stepOut", { granularity: "statement" });
  }

  // Asks the running engine to pause; the pause is shown.
  pause() {
    if (this.state !== "running") return;
    if (this.quiet) this.quiet.show = true;
    else this.session.request("pause", { threadId: 1 });
  }

  sendBreakpoints(s) {
    const bps = this.config.breakpoints;
    const sent = bps.map(({ alg, path }) => (path ? { alg, path } : { alg }));
    return s.request("setSpecBreakpoints", { breakpoints: sent }).then((r) => {
      if (s !== this.session || !r?.success || bps !== this.config.breakpoints) return;
      this.bpStatus = r.body.breakpoints;
      this.emit("breakpoints");
    });
  }

  // The program's line breakpoints [{line, column?}].
  lineBreakpoints() {
    const name = this.config.program?.name;
    return (name && this.config.lineBreakpoints[name]) || [];
  }

  // The line line breakpoint i is shown at: where it resolved, else where it was set.
  lineOf(i) {
    const st = this.lineStatus[i];
    return st?.verified ? st.line : this.lineBreakpoints()[i]?.line;
  }

  sendLineBreakpoints(s) {
    const bps = this.lineBreakpoints();
    const sent = bps.map(({ line, column }) => (column ? { line, column } : { line }));
    return s.request("setBreakpoints", { source: { path: s.program }, breakpoints: sent }).then((r) => {
      if (s !== this.session || !r?.success || bps !== this.lineBreakpoints()) return;
      this.lineStatus = r.body.breakpoints.map((b) => this.lineChanged.get(b.id) ?? b);
      this.emit("breakpoints");
    });
  }

  // A `breakpoint` event: the line breakpoint's new status (kept by id if the reply is
  // still to come).
  lineBreakpointChanged(bp) {
    if (!bp) return;
    this.lineChanged.set(bp.id, bp);
    const i = this.lineStatus.findIndex((b) => b.id === bp.id);
    if (i < 0) return;
    this.lineStatus[i] = bp;
    this.emit("breakpoints");
  }

  setLineBreakpoints(bps) {
    const name = this.config.program?.name;
    if (!name) return Promise.resolve();
    this.config.lineBreakpoints = { ...this.config.lineBreakpoints, [name]: bps };
    this.lineStatus = [];
    this.emit("breakpoints");
    return this.configure((s) => this.sendLineBreakpoints(s));
  }

  // A line breakpoint on line n removed if one is shown there, else added.
  toggleLine(n) {
    const bps = this.lineBreakpoints();
    const i = bps.findIndex((_, j) => this.lineOf(j) === n);
    return this.setLineBreakpoints(i >= 0 ? bps.filter((_, j) => j !== i) : [...bps, { line: n }]);
  }

  sendFilters(s) {
    const filters = this.config.filters;
    return s.request("setExceptionBreakpoints", { filters }).then((r) => {
      if (s !== this.session || !r?.success || filters !== this.config.filters) return;
      this.filterStatus = r.body.breakpoints ?? [];
      this.emit("filters");
    });
  }

  // `send(s)` now, or while the run goes on at a pause not shown: `pause`, `send`,
  // `continue`. A pause the run reached first (a breakpoint, its end) is shown as usual.
  // A session started after the change sent the configuration at its start: skipped.
  configure(send) {
    const s = this.session;
    this.chain = this.chain.then(async () => {
      if (!s || s !== this.session) return;
      if (this.state !== "running") return send(s);
      this.quiet = { held: null, show: false };
      const r = await s.request("pause", { threadId: 1 });
      if (s !== this.session) return;
      const { held, show } = this.quiet;
      this.quiet = null;
      if (!r) return;
      const done = send(s);
      if (r?.success && held?.reason === "pause" && !show) s.request("continue", { threadId: 1 });
      else if (held) this.show(s, held);
      return done;
    });
    return this.chain;
  }

  setBreakpoints(breakpoints) {
    this.config.breakpoints = breakpoints;
    this.bpStatus = [];
    this.emit("breakpoints");
    return this.configure((s) => this.sendBreakpoints(s));
  }

  setFilters(filters) {
    this.config.filters = filters;
    this.filterStatus = [];
    this.emit("filters");
    return this.configure((s) => this.sendFilters(s));
  }
}
