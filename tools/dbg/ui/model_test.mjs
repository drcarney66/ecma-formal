#!/usr/bin/env node
// tools/dbg/ui/model.mjs against native ecma-dbg as a child process (client.mjs's
// native-process transport), on the programs of tests/dbg:
//
//   node tools/dbg/ui/model_test.mjs --native .lake/build/bin/ecma-dbg [--dir tests/dbg]
//
// - stepping.js: selftest.mjs's scenario with the snapshot checked: a breakpoint at
//   sec-evaluatecall 3, the frames, the JS position, the Slots, EvaluateCall's listing
//   and one refused, a breakpoint toggled at step 5, stepIn, stepOut, a slot expanded,
//   another frame selected, continue to step 5 and to the end, and a restart;
// - spin.js: a pause asked for while it runs; a breakpoint set while it runs (the
//   model's own pause is not shown); stopped;
// - list.js: output at a pause, the debugger filter, a List paged by start and count,
//   and as a heap cell;
// - heap.js: the heap pane's requests: a new object cell by kind, `o.a` changed between
//   two pauses (old 1, new 2, from specDiff), the heap paged, specState, the contexts;
//   relaunched after a killed run and after a paused one, with the breakpoints and filters
//   changed just before: its first stop the session's first pause (no diff, none hidden);
// - tdz.js: a let binding in its TDZ, then initialized and marked changed;
// - jsstack.js: the JS stack at a getter's call (in map's callback three calls deep): its
//   frames, one selected (its innermost spec frame, its position), one whose spec frames
//   are past the first page, and a spec frame selected again;
// - linebp.js: line breakpoints pending at the entry, then resolved by `breakpoint`
//   events (the blank line moved), the breakable lines, a hit on each loop iteration, one
//   toggled off while paused, statement stepping into f and out;
// - eval.js: stepIn into direct eval code opens its source (`eval #1`, its text from
//   `source`) and shows it; the JS stack's (eval) with its position; (script) selected
//   shows the program, the pause's frame again the eval code; a step in it; stepIn into a
//   Function's body opens `Function #1`;
// - bundle.js: a d8 bundle's entry module is the program and its other modules are
//   listed as sources with their texts (`loadedSource`); a line breakpoint in the entry,
//   stepIn into a module shows it, the JS stack's (module);
// - source.mjs's line table (CR LF, U+2028, an astral code point), heap.mjs's diff line
//   and parts, with no engine.

import { readFileSync } from "node:fs";
import { join } from "node:path";
import { DbgClient } from "../client.mjs";
import { HEAP_PAGE, KIND_PAGE, diffLine, diffParts, diffRows, listLength, parseAddr } from "./heap.mjs";
import { FRAME_PAGE, Model, cellOf } from "./model.mjs";
import { lineTable, programName, utf16 } from "./source.mjs";
import { programRoot, splitContexts } from "./state.mjs";

let failed = 0;
let passed = 0;

function check(cond, what) {
  if (cond) passed++;
  else {
    failed++;
    console.log(`FAIL ${what}`);
  }
}

const paused = (m) => m.state === "paused";
const ended = (m) => m.state === "terminated" || m.state === "ended";
const framesIn = (m) => m.snap?.totalFrames != null;
const slotsIn = (m) => {
  const sc = m.snap?.scopes.get(m.snap.selected);
  const slots = sc?.find((x) => x.name === "Slots");
  return slots && m.loaded(slots.variablesReference);
};
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

function slotsOf(m) {
  const slots = m.snap.scopes.get(m.snap.selected).find((x) => x.name === "Slots");
  return m.loaded(slots.variablesReference);
}

async function stepping(client, dir) {
  const source = readFileSync(join(dir, "stepping.js"), "utf8");
  const m = new Model(client, {
    program: { name: "stepping.js", source },
    breakpoints: [{ alg: "sec-evaluatecall", path: "3" }],
  });
  m.start();
  await m.until((m) => paused(m) && framesIn(m) && slotsIn(m));
  const st = m.snap.stopped;
  check(st.reason === "breakpoint" && st.spec.secId === "sec-evaluatecall" && st.spec.path === "3", "stepping: the breakpoint's stop");
  check(m.bpStatus[0]?.verified && m.bpStatus[0].resolved?.[0] === "sec-evaluatecall#0", "stepping: the breakpoint verified");
  check(m.snap.frames[0].name === "EvaluateCall" && m.snap.totalFrames === m.snap.frames.length, "stepping: the frames");
  check(m.snap.frames.length <= FRAME_PAGE, "stepping: one page of frames");
  const js = m.jsFrame();
  check(js && js.line === 4 && js.spec.node.lo === 30 && js.spec.node.hi === 34, "stepping: the JS position f(2)");
  const slots = slotsOf(m);
  check(slots.map((v) => v.name).join() === "func,thisValueRef,argumentListNode,tailPosition,thisValue,refEnv,argList", "stepping: the Slots");
  check(slots.find((v) => v.name === "argList").value === "unbound", "stepping: argList unbound");

  check(m.listing("sec-evaluatecall", 0) === undefined, "stepping: the listing asked for");
  await m.until((m) => m.listing("sec-evaluatecall", 0) !== undefined && m.listing("sec-no-such-clause", 0) !== undefined);
  const l = m.listing("sec-evaluatecall", 0);
  const flat = (ss) => ss.flatMap((x) => [x.path, ...flat(x.steps ?? [])]);
  check(l?.name === "EvaluateCall" && flat(l.steps).join() === "1,1.a,1.a.i,1.b,1.b.i,1.b.ii,1.b.iii,2,2.a,3,4,5,6,7", "stepping: EvaluateCall's listing");
  check(l?.steps[2].path === "3" && l.steps[2].text === st.spec.text, "stepping: the listing's step 3 is the stop's");
  check(m.listing("sec-no-such-clause", 0) === null, "stepping: a listing refused");
  await m.toggleBreakpoint("sec-evaluatecall", 0, "5");
  const added = m.config.breakpoints[1];
  check(m.config.breakpoints.length === 2 && added.alg === "sec-evaluatecall#0" && added.path === "5" && m.bpStatus[1]?.verified, "stepping: a step's breakpoint added");

  check(m.stepIn(), "stepping: stepIn accepted");
  check(m.state === "running" && m.snap === null, "stepping: running after stepIn");
  await m.until((m) => paused(m) && framesIn(m) && slotsIn(m));
  let sp = m.snap.stopped.spec;
  check(sp.alg === "ArgumentListEvaluation" && sp.path === "1" && sp.depth === 6, "stepping: stepIn's stop");
  check(sp.diff && Array.isArray(sp.diff.newCells), "stepping: the diff");

  m.stepOut();
  await m.until((m) => paused(m) && framesIn(m) && slotsIn(m));
  sp = m.snap.stopped.spec;
  check(sp.secId === "sec-evaluatecall" && sp.depth === 5, `stepping: stepOut's stop (${sp.secId} ${sp.path} ${sp.depth})`);
  const func = slotsOf(m).find((v) => v.name === "func");
  const parts = await m.variables(func.variablesReference);
  check(parts && parts.length > 0, "stepping: a slot expanded");
  check(m.loaded(func.variablesReference) === parts, "stepping: the parts cached");

  m.selectFrame(1);
  await m.until((m) => m.snap.scopes.has(1) && slotsIn(m));
  check(m.frame().id === 1 && m.snap.scopes.get(1).some((x) => x.name === "Step"), "stepping: frame 1's scopes");
  check(m.moreFrames() === null, "stepping: no more frames");

  m.cont();
  await m.until((m) => paused(m) || ended(m));
  sp = m.snap?.stopped;
  check(sp?.reason === "breakpoint" && sp.spec.secId === "sec-evaluatecall" && sp.spec.path === "5", "stepping: the step's breakpoint's stop");
  await m.toggleBreakpoint("sec-evaluatecall", 0, "5");
  check(m.config.breakpoints.length === 1 && m.config.breakpoints[0].path === "3", "stepping: the step's breakpoint removed");
  m.cont();
  await m.until(ended);
  check(m.state === "terminated" && m.ending.outcome === "normal: 2" && m.ending.exitCode === 0, "stepping: terminated");
  check(m.output.some((o) => o.text.includes("normal: 2")), "stepping: the console's end");

  let endless = 0;
  m.on("change", () => m.state === "terminated" && !m.ending && endless++);
  m.restart();
  await m.until((m) => paused(m) && framesIn(m));
  check(m.snap.stopped.spec.path === "3" && m.output.length === 0, "stepping: restart stops at the breakpoint again");
  check(endless === 0, "stepping: restart after the end leaves no terminated state without its ending");
  m.stop();
  check(m.state === "ended" && m.session === null, "stepping: stopped");
}

async function pausing(client, dir) {
  const source = readFileSync(join(dir, "spin.js"), "utf8");
  const m = new Model(client, { program: { name: "spin.js", source } });
  m.start();
  await sleep(500);
  check(m.state === "running", "pause: running");
  m.pause();
  await m.until(paused);
  check(m.snap.stopped.reason === "pause", "pause: a pause asked for");
  m.cont();
  await sleep(300);
  const shown = [];
  m.on("change", (w) => w === "pause" && m.snap && shown.push(m.snap.stopped.reason));
  await m.setBreakpoints([{ alg: "sec-postfix-increment-operator-runtime-semantics-evaluation" }]);
  await m.until((m) => paused(m) || ended(m));
  check(m.state === "paused" && shown.join() === "breakpoint", `pause: the model's pause not shown (${shown})`);
  check(m.bpStatus[0]?.verified, "pause: the breakpoint verified");
  m.stop();
  check(m.state === "ended" && m.session === null, "pause: stopped");
}

async function listing(client, dir) {
  const source = readFileSync(join(dir, "list.js"), "utf8");
  const m = new Model(client, {
    program: { name: "list.js", source },
    breakpoints: [{ alg: "OrdinaryCallEvaluateBody", path: "1" }],
    filters: ["debugger"],
  });
  m.start();
  await m.until(paused);
  check(m.snap.stopped.description === "debugger statement", "list: the debugger filter");
  check(m.output.some((o) => o.category === "stdout" && o.text === "one\n"), "list: output at a pause");
  m.cont();
  await m.until(paused);
  m.cont();
  await m.until((m) => paused(m) && slotsIn(m));
  const args = slotsOf(m).find((v) => v.name === "argList");
  check(args.indexedVariables === 5, "list: the List's length");
  const page = await m.variables(args.variablesReference, 1, 2);
  check(page.map((v) => `${v.name}=${v.value}`).join() === "[1]=11,[2]=12", "list: a page");
  const addr = cellOf(args);
  const cell = (await m.heap(addr, 1)).cells[0];
  check(cell.kind === "list" && listLength(cell.type) === 5 && cell.variablesReference === args.variablesReference, `list: its cell (${cell.type})`);
  const tail = await m.variables(cell.variablesReference, 3, 100);
  check(tail.map((v) => v.value).join() === "13,14", "list: the cell's last page");
  m.stop();
}

// The "Execution contexts" scope of frame 0.
async function contextsOf(m) {
  await m.until((m) => m.snap?.scopes.has(0));
  const sc = m.snap.scopes.get(0).find((x) => x.name === "Execution contexts");
  return splitContexts(await m.variables(sc.variablesReference));
}

async function heap(client, dir) {
  const source = readFileSync(join(dir, "heap.js"), "utf8");
  const m = new Model(client, { program: { name: "heap.js", source }, filters: ["debugger"] });
  m.start();
  await m.until(paused);
  check(m.diff() === null && diffParts(m.diff()).length === 0, "heap: no diff at the first pause");
  m.cont();
  await m.until(paused);
  let diff = m.diff();
  const [lo, hi] = diff.newCells;
  check(hi > lo && diffLine(diff).startsWith(`since the last pause: ${hi - lo} new cells`), `heap: the new cells (${diffLine(diff)})`);
  const objs = await m.heap(lo, KIND_PAGE, "object");
  check(objs.heapSize === hi && objs.cells.every((c) => c.kind === "object" && c.addr >= lo), "heap: the new objects");
  const o = objs.cells.find((c) => c.summary.endsWith("{a}"));
  check(o && o.type === "Object" && o.variablesReference === o.addr + 1, `heap: the object {a: 1} (${objs.cells.map((c) => c.summary)})`);
  check(m.heap(lo, KIND_PAGE, "object") === m.heap(lo, KIND_PAGE, "object"), "heap: specHeap cached");
  let a = (await m.variables(o.variablesReference)).find((v) => v.name === "a");
  check(a.value === "1" && a.type.startsWith("data property"), "heap: o.a is 1");
  const rec = cellOf(a);
  check(rec !== null && rec >= lo && rec < hi, "heap: o.a's attribute Record is a new cell");
  const page = await m.heap(0, HEAP_PAGE);
  check(page.cells.length === HEAP_PAGE && page.cells[0].addr === 0 && page.cells.at(-1).addr === HEAP_PAGE - 1, "heap: a page");
  const lists = await m.heap(HEAP_PAGE, KIND_PAGE, "list");
  check(lists.cells.length > 0 && lists.cells.every((c) => c.kind === "list" && c.addr >= HEAP_PAGE && c.addr < HEAP_PAGE + KIND_PAGE), "heap: a page of Lists");

  m.cont();
  await m.until(paused);
  diff = m.diff();
  check(diff.changed.includes(rec) && !diff.truncated && !diff.stackChanged, `heap: o.a's Record changed (${JSON.stringify(diff)})`);
  check(diffParts(diff).map((p) => p.view.mode).join() === "new,changed", "heap: the summary's links");
  const d = await m.spec("specDiff", { addr: rec });
  const value = diffRows(d).find((r) => r.name === "[[Value]]");
  check(value && value.old === "1" && value.now === "2" && value.changed && d.changed.join() === "[[Value]]", `heap: [[Value]] 1 → 2 (${JSON.stringify(value)})`);
  const od = await m.spec("specDiff", { addr: o.addr });
  const ar = diffRows(od).find((r) => r.name === "a");
  check(ar && ar.old === "1" && ar.now === "2" && ar.changed, `heap: o's a 1 → 2 (${JSON.stringify(ar)})`);
  a = (await m.variables(o.variablesReference)).find((v) => v.name === "a");
  check(a.value === "2" && a.presentationHint?.attributes?.includes("changed"), "heap: o.a marked changed");

  const st = await m.spec("specState");
  const root = programRoot(st.roots);
  check(root && root.production === "Script : ScriptBody?" && root.lo === 0 && root.hi > 0, "state: the program's root");
  check(st.agent.name === "agent" && cellOf(st.agent) !== null && "transitions" in st.host, "state: the agent and host");
  const { contexts, facts } = await contextsOf(m);
  check(contexts.length === st.contexts && contexts[0].name.endsWith(" running"), `state: the running context first (${contexts.map((v) => v.name)})`);
  check(facts.map((v) => v.name).includes("current Realm") && !facts.some((v) => v.name.startsWith("[")), "state: the derived facts");
  m.cont();
  await m.until(ended);
  check(m.ending?.outcome === "normal: 2", "heap: the end");
}

// heap.js's first stop: the debugger statement's, no diff, none hidden before it.
async function firstStop(m, what) {
  const reasons = [];
  m.session.on("message", (e) => e.type === "event" && e.event === "stopped" && reasons.push(e.body.reason));
  await m.until(paused);
  const ok = m.snap.stopped.description === "debugger statement" && reasons.join() === "breakpoint";
  check(ok && diffLine(m.diff()) === "first pause: no diff", `relaunch: ${what} (${reasons}; ${diffLine(m.diff())})`);
}

// heap.js after a killed run and after a paused one, with the breakpoints and filters
// changed just before the start: its first stop is the session's first pause.
async function relaunch(client, dir) {
  const source = readFileSync(join(dir, "heap.js"), "utf8");
  const m = new Model(client, { program: { name: "heap.js", source }, filters: ["debugger"] });
  m.start();
  await m.until(paused);
  m.stop();
  m.setBreakpoints([]);
  m.setFilters(["debugger"]);
  m.start();
  await firstStop(m, "after a killed run");
  m.setBreakpoints([{ alg: "sec-evaluatecall", path: "3" }]);
  m.setBreakpoints([]);
  m.start();
  await firstStop(m, "after a paused run");
  m.stop();
}

async function tdz(client, dir) {
  const source = readFileSync(join(dir, "tdz.js"), "utf8");
  const m = new Model(client, { program: { name: "tdz.js", source }, filters: ["debugger"] });
  m.start();
  await m.until(paused);
  const field = async (v, name) => (await m.variables(v.variablesReference)).find((x) => x.name === name);
  const { facts } = await contextsOf(m);
  const ctx = facts.find((v) => v.name === "running execution context");
  const decl = await field(await field(ctx, "[[LexicalEnvironment]]"), "[[DeclarativeRecord]]");
  let x = await field(decl, "x");
  check(x?.value === "TDZ" && x.type.includes("uninitialized (TDZ)"), `tdz: x in its TDZ (${x?.value})`);
  check((await m.heap(cellOf(decl), 1)).cells[0].kind === "env", "tdz: the record is an env cell");
  m.cont();
  await m.until(paused);
  x = await field(decl, "x");
  check(x?.value === "1" && x.type.includes("initialized") && x.presentationHint?.attributes?.includes("changed"), `tdz: x initialized, changed (${x?.value})`);
  m.stop();
}

async function jsstack(client, dir) {
  const source = readFileSync(join(dir, "jsstack.js"), "utf8");
  const m = new Model(client, { program: { name: "jsstack.js", source }, breakpoints: [{ alg: "OrdinaryGet", path: "7" }] });
  m.start();
  await m.until((m) => paused(m) && framesIn(m) && m.snap.jsFrames);
  // The first call of a getter is map's ArraySpeciesCreate's, of Array's @@species.
  check(m.snap.jsFrames.map((f) => f.name).join() === "map,f,f,f,(script),(host)", "jsstack: @@species's getter called in map");
  m.cont();
  await m.until((m) => paused(m) && framesIn(m) && m.snap.jsFrames);
  const js = m.snap.jsFrames;
  const names = js.map((f) => f.name).join();
  check(names === "(anonymous),map,f,f,f,(script),(host)", `jsstack: the frames (${names})`);
  check(js[0].spec.frames.lo === 0 && js.every((f, i) => i === 0 || f.spec.frames.lo === js[i - 1].spec.frames.hi), "jsstack: the spec ranges adjacent");
  check(js[1].inBuiltin === "Array.prototype.map" && js[1].line === 0, "jsstack: map is a built-in's, with no position");
  check(m.jsFrameOf(0) === js[0] && m.jsPosition()?.line === 4, `jsstack: the innermost position (${m.jsPosition()?.line})`);
  await m.selectJsFrame(2);
  check(m.snap.selected === js[2].spec.frames.lo && m.snap.jsSelected === 2, "jsstack: f's innermost spec frame selected");
  const at = m.jsPosition();
  check(at?.line === 3 && at.lo === js[2].lo && at.hi === js[2].hi, `jsstack: f's position (${JSON.stringify(at)})`);
  await m.selectJsFrame(1);
  check(m.jsPosition() === null, "jsstack: map has no position");
  const host = js.length - 1;
  check(js[host].spec.frames.lo >= FRAME_PAGE, `jsstack: (host)'s frames past the first page (${js[host].spec.frames.lo})`);
  await m.selectJsFrame(host);
  check(m.snap.frames.length > js[host].spec.frames.lo && m.frame()?.id === js[host].spec.frames.lo, "jsstack: the frames loaded to (host)'s");
  m.selectFrame(0);
  check(m.snap.jsSelected === null && m.jsPosition()?.line === 4, "jsstack: a spec frame selected again");
  m.stop();
}

async function linebp(client, dir) {
  const source = readFileSync(join(dir, "linebp.js"), "utf8");
  const m = new Model(client, { program: { name: "linebp.js", source }, lineBreakpoints: { "linebp.js": [{ line: 7 }, { line: 9 }] }, stopOnEntry: true });
  m.start();
  await m.until((m) => paused(m) && m.lineStatus.length === 2);
  check(m.snap.stopped.reason === "entry" && m.lineStatus.every((b) => !b.verified && b.message === "pending"), "linebp: pending at the entry");
  check(m.locations === null, "linebp: no locations before the parse");
  m.cont();
  await m.until(paused);
  let st = m.snap.stopped;
  check(st.reason === "breakpoint" && st.js.line === 7 && st.hitBreakpointIds?.[0] === m.lineStatus[0].id, `linebp: line 7 hit (${st.js?.line})`);
  check(m.lineStatus[0].verified && m.lineOf(0) === 7 && m.lineStatus[1].verified && m.lineOf(1) === 10, "linebp: resolved, 9 moved to 10");
  await m.until((m) => m.locations);
  check([...m.locations].sort((a, b) => a - b).join() === "2,3,5,6,7,10,11", `linebp: breakable lines (${[...m.locations]})`);
  m.cont();
  await m.until(paused);
  check(m.snap.stopped.js.line === 7, "linebp: line 7 on the second iteration");
  await m.toggleLine(7);
  check(m.lineBreakpoints().length === 1 && m.lineBreakpoints()[0].line === 9, "linebp: line 7 toggled off");
  m.cont();
  await m.until((m) => paused(m) || ended(m));
  st = m.snap?.stopped;
  check(st?.reason === "breakpoint" && st.js.line === 10, `linebp: line 10 next (${st?.js?.line})`);
  m.jsIn();
  await m.until(paused);
  st = m.snap.stopped;
  check(st.reason === "step" && st.js.line === 2 && st.js.statement?.line === 2, "linebp: statement stepIn into f");
  m.jsOut();
  await m.until(paused);
  check(m.snap.stopped.js.line === 10 && m.snap.stopped.js.contexts === 2, "linebp: statement stepOut at the call");
  await m.setLineBreakpoints([]);
  m.cont();
  await m.until(ended);
  check(m.ending?.outcome.startsWith("normal"), "linebp: the end");
  m.stop();
}

async function evalCode(client, dir) {
  const source = readFileSync(join(dir, "eval.js"), "utf8");
  const m = new Model(client, { program: { name: "eval.js", source }, lineBreakpoints: { "eval.js": [{ line: 2 }, { line: 4 }] } });
  m.start();
  await m.until(paused);
  check(m.snap.stopped.js.line === 2 && m.sourceShown === 0 && m.sources.size === 0, "eval: at line 2, the program shown");
  m.jsIn();
  await m.until((m) => paused(m) && m.snap.jsFrames);
  let st = m.snap.stopped;
  const ref = st.js.source?.sourceReference;
  check(st.js.source?.name === "eval #1" && ref > 0 && st.js.line === 1, `eval: stepIn into the eval code (${JSON.stringify(st.js.source)} ${st.js.line})`);
  check(m.sourceShown === ref, "eval: its source shown");
  await m.until((m) => m.sources.get(ref)?.text !== null);
  check(m.sources.get(ref).text === "var c = a + 1;\nc * 2", `eval: its text (${JSON.stringify(m.sources.get(ref).text)})`);
  const js = m.snap.jsFrames;
  check(js[0].name === "(eval)" && js[0].source?.sourceReference === ref && js[0].line === 1, `eval: the JS stack's (eval) (${JSON.stringify(js[0])})`);
  const at = m.jsPosition();
  check(at?.ref === ref && at.line === 1 && at.lo === 0 && at.hi === 14, `eval: the position (${JSON.stringify(at)})`);
  await m.selectJsFrame(1);
  check(m.sourceShown === 0 && m.jsPosition()?.ref === 0 && m.jsPosition()?.line === 2, "eval: (script) selected shows the program");
  m.selectFrame(0);
  check(m.sourceShown === ref, "eval: the pause's frame shows the eval code again");
  m.jsIn();
  await m.until(paused);
  st = m.snap.stopped;
  check(st.js.source?.sourceReference === ref && st.js.line === 2 && st.js.lo === 15 && st.js.hi === 20, `eval: its next statement (${st.js.line})`);
  m.showSource(0);
  check(m.sourceShown === 0, "eval: the program's tab");
  m.cont();
  await m.until(paused);
  check(m.snap.stopped.js.line === 4 && m.sourceShown === 0, "eval: line 4");
  m.jsIn();
  await m.until(paused);
  st = m.snap.stopped;
  const fref = st.js.source?.sourceReference;
  check(st.js.source?.name === "Function #1" && st.js.line === 3 && m.sourceShown === fref && m.sources.size === 2, `eval: stepIn into the Function's body (${JSON.stringify(st.js.source)} ${st.js.line})`);
  await m.until((m) => m.sources.get(fref)?.text !== null);
  check(m.sources.get(fref).text.startsWith("function anonymous(x\n) {"), "eval: the Function's text");
  await m.setLineBreakpoints([]);
  m.cont();
  await m.until(ended);
  check(m.ending?.outcome.startsWith("normal"), "eval: the end");
  m.stop();
}

async function bundle(client, dir) {
  const source = readFileSync(join(dir, "bundle.js"), "utf8");
  const m = new Model(client, { program: { name: "bundle.js", source }, lineBreakpoints: { "bundle.js": [{ line: 2 }] } });
  m.start();
  await m.until((m) => paused(m) && m.program?.name === "main.mjs" && [...m.sources.values()].every((x) => x.text !== null));
  check(m.program.source === 'import { show } from "./lib/show.mjs";\nshow(21);\n', `bundle: the entry module is the program (${JSON.stringify(m.program)})`);
  const mods = [...m.sources.values()];
  check(mods.map((x) => x.name).join() === "lib/math.mjs,lib/show.mjs" && mods.every((x) => x.module), `bundle: its modules listed (${mods.map((x) => x.name)})`);
  check(mods[0].text === "export function double(x) {\n  return x * 2;\n}\n", `bundle: lib/math.mjs's text (${JSON.stringify(mods[0].text)})`);
  check(m.snap.stopped.js.line === 2 && m.sourceShown === 0, "bundle: at the entry's line 2, the entry shown");
  m.jsIn();
  await m.until((m) => paused(m) && m.snap.jsFrames);
  const st = m.snap.stopped;
  check(st.js.source?.name === "lib/show.mjs" && st.js.line === 3 && m.sourceShown === mods[1].ref, `bundle: stepIn into lib/show.mjs, shown (${JSON.stringify(st.js.source)} ${st.js.line})`);
  check(m.snap.jsFrames[1]?.name === "(module)" && m.snap.jsFrames[1].source?.name === "main.mjs", "bundle: the JS stack's (module)");
  check(m.sources.size === 2, "bundle: no source opened twice");
  m.cont();
  await m.until(ended);
  check(m.ending?.outcome === "normal: undefined" && m.output.some((o) => o.text === "42\n"), "bundle: the end");
  m.stop();
}

function pure() {
  const t = lineTable("a\r\nb\u2028\u{1F600}c\rd\n");
  const lines = t.lines.map(({ start, end }) => `${start}-${end}`).join();
  check(lines === "0-1,3-4,5-8,9-10,11-11", `lines: split (${lines})`);
  // Code points: a CR LF b LS 😀 c CR d LF; 😀 is two UTF-16 units.
  check(utf16(t, 5) === 5 && utf16(t, 6) === 7 && utf16(t, 7) === 8 && utf16(t, 10) === 11, "lines: code points as UTF-16");
  check(utf16(t, 99) === 11, "lines: past the end");
  check(lineTable("").lines.length === 1, "lines: empty");
  check(programName("my file.js") === "my_file.js" && programName(".x") === "_x" && programName("") === "program.js", "programName");
  check(diffLine(null) === "first pause: no diff", "diffLine: first");
  const d = diffLine({ newCells: [3, 5], changed: [7], truncated: true, stackChanged: true });
  check(d === "since the last pause: 2 new cells, 1+ changed, stack changed", `diffLine: ${d}`);
  check(diffLine({ newCells: [0, 0] }).includes("0 changed"), "diffLine: no changed");
  check(diffParts({ newCells: [4, 5], changed: [] }).map((p) => p.text).join() === "1 new cell,0 changed", "diffParts");
  check(listLength("List (13)") === 13 && listLength("Object") === 0, "listLength");
  check(parseAddr(" #12") === 12 && parseAddr("7") === 7 && parseAddr("x") === null, "parseAddr");
  const rows = diffRows({ old: null, new: { variables: [{ name: "a", value: "1" }] }, changed: ["a"] });
  check(rows.length === 1 && rows[0].old === null && rows[0].changed, "diffRows: a new cell");
  const sp = splitContexts([{ name: "[0]" }, { name: "[1] running" }, { name: "resumed" }]);
  check(sp.contexts.map((v) => v.name).join() === "[1] running,[0]" && sp.facts.length === 1, "splitContexts");
  check(cellOf({ variablesReference: 5 }) === 4 && cellOf({ variablesReference: 2 ** 44 + 3 }) === null && cellOf({}) === null, "cellOf");
}

async function main() {
  const args = process.argv.slice(2);
  let bin = null;
  let dir = "tests/dbg";
  for (let i = 0; i < args.length; i++) {
    if (args[i] === "--native") bin = args[++i];
    else if (args[i] === "--dir") dir = args[++i];
  }
  if (!bin) {
    console.error("usage: model_test.mjs --native ECMA_DBG [--dir DIR]");
    process.exit(2);
  }
  pure();
  const client = DbgClient.spawn(bin);
  for (const [name, t] of [["stepping", stepping], ["pause", pausing], ["list", listing], ["heap", heap], ["relaunch", relaunch], ["tdz", tdz], ["jsstack", jsstack], ["linebp", linebp], ["eval", evalCode], ["bundle", bundle]]) {
    const before = failed;
    try {
      await t(client, dir);
    } catch (e) {
      failed++;
      console.log(`FAIL ${name}: ${e.message}`);
    }
    console.log(`${failed === before ? "ok" : "FAIL"} ${name}`);
  }
  console.log(`${passed} checks passed, ${failed} failed`);
  process.exit(failed ? 1 : 0);
}

main();
