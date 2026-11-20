#!/usr/bin/env node
// The demo's scripts (script.mjs) on tools/dbg/ui/model.mjs, in node: native ecma-dbg as a
// child process (client.mjs's native-process transport) or its WebAssembly build in a node
// Worker. Each script's breakpoints are set, its program started, and at each stop its
// action is taken and what the stop shows (observe) checked against the script's.
//
//   node tools/dbg/demo/demo_test.mjs --native .lake/build/bin/ecma-dbg [--dump] [NAME.js...]
//   node tools/dbg/demo/demo_test.mjs --wasm-node build/web/ecma-dbg-web.mjs
//
// --dump prints each stop's observation as a JSON line too.

import { readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { DbgClient } from "../client.mjs";
import { Model, cellOf } from "../ui/model.mjs";
import { DEMOS, mismatches } from "./script.mjs";

const here = dirname(fileURLToPath(import.meta.url));

const paused = (m) => m.state === "paused";
const ended = (m) => m.state === "terminated" || m.state === "ended";
const slotsOf = (m) => {
  const sc = m.snap?.scopes.get(0)?.find((x) => x.name === "Slots");
  return sc ? m.loaded(sc.variablesReference) : undefined;
};
// A pause's frames, JS stack, frame 0's Slots and listing loaded.
const settled = (m) =>
  paused(m) && m.snap.totalFrames !== null && m.snap.jsFrames && slotsOf(m) &&
  m.listing(m.snap.stopped.spec.secId, m.snap.stopped.spec.idx ?? 0) !== undefined;

// What a stop shows, as script.mjs's stops name it.
// `cells`: the slots whose heap cells are expanded.
async function observe(m, cells) {
  const st = m.snap.stopped;
  const s = st.spec;
  const pos = m.jsPosition();
  const cps = [...m.program.source];
  const slots = slotsOf(m);
  const l = m.listing(s.secId, s.idx ?? 0);
  const flat = (ss) => ss.flatMap((x) => [x.path, ...flat(x.steps ?? [])]);
  const o = {
    reason: st.reason,
    alg: s.alg,
    path: s.path,
    secId: s.secId,
    text: s.text,
    current: l && flat(l.steps).includes(s.path) ? s.path : null,
    line: pos && !pos.ref ? pos.line : null,
    node: pos && !pos.ref ? cps.slice(pos.lo, pos.hi).join("") : null,
    frames: m.snap.frames.map((f) => `${f.name} ${f.spec.path}`),
    js: m.snap.jsFrames.map((f) => f.name),
    slots: Object.fromEntries(slots.map((v) => [v.name, v.value])),
  };
  o.cell = {};
  for (const name of cells) {
    const v = slots.find((x) => x.name === name);
    if (!v || cellOf(v) === null) continue;
    const parts = await m.variables(v.variablesReference);
    o.cell[name] = Object.fromEntries((parts ?? []).map((p) => [p.name, p.value]));
  }
  return o;
}

const ACTIONS = {
  continue: (m) => m.cont(),
  next: (m) => m.next(),
  in: (m) => m.stepIn(),
  out: (m) => m.stepOut(),
  jsNext: (m) => m.jsNext(),
  jsIn: (m) => m.jsIn(),
  jsOut: (m) => m.jsOut(),
};

async function walk(client, demo, dump, fail) {
  const source = readFileSync(join(here, demo.program), "utf8");
  const m = new Model(client, {
    program: { name: demo.program, source },
    breakpoints: demo.breakpoints ?? [],
    lineBreakpoints: demo.lines ? { [demo.program]: demo.lines.map((line) => ({ line })) } : {},
    filters: demo.filters ?? [],
    stopOnEntry: false,
  });
  m.start();
  for (const [i, stop] of demo.stops.entries()) {
    const what = `${demo.program} stop ${i + 1}`;
    if (i > 0 && !ACTIONS[stop.do](m)) throw new Error(`${what}: ${stop.do} refused in state ${m.state}`);
    await m.until((m) => settled(m) || ended(m));
    if (!paused(m)) throw new Error(`${what}: ended (${m.ending?.outcome ?? m.state}) before the stop`);
    const o = await observe(m, Object.keys(stop.cell ?? {}));
    if (dump) console.log(JSON.stringify({ stop: what, do: stop.do, ...o }));
    for (const f of mismatches(stop, o)) fail(`${what} (${stop.alg} ${stop.path}): ${f}`);
  }
  if (!ACTIONS[demo.endBy ?? "continue"](m)) throw new Error(`${demo.program}: the last continue refused`);
  await m.until(ended);
  if (m.ending?.outcome !== demo.end) fail(`${demo.program}: ended ${m.ending?.outcome ?? m.state}, not ${demo.end}`);
  m.stop();
}

async function main() {
  const args = process.argv.slice(2);
  let native = null;
  let web = null;
  let dump = false;
  const only = [];
  for (let i = 0; i < args.length; i++) {
    if (args[i] === "--native") native = args[++i];
    else if (args[i] === "--wasm-node") web = args[++i];
    else if (args[i] === "--dump") dump = true;
    else only.push(args[i]);
  }
  if (!native === !web) {
    console.error("usage: demo_test.mjs (--native ECMA_DBG | --wasm-node ECMA_DBG_WEB.mjs) [--dump] [NAME.js...]");
    process.exit(2);
  }
  let client;
  if (native) client = DbgClient.spawn(native);
  else {
    const mjs = web.endsWith(".mjs") ? web : `${web}.mjs`;
    client = await DbgClient.load(resolve(mjs).replace(/\.mjs$/, ".wasm"), { glue: resolve(mjs) });
  }
  let failed = 0;
  let checks = 0;
  for (const demo of DEMOS.filter((d) => !only.length || only.includes(d.program))) {
    const before = failed;
    const fail = (why) => {
      failed++;
      console.log(`FAIL ${why}`);
    };
    try {
      await walk(client, demo, dump, fail);
    } catch (e) {
      fail(`${demo.program}: ${e.message}`);
    }
    checks += demo.stops.length + 1;
    console.log(`${failed === before ? "ok" : "FAIL"} ${demo.program}`);
  }
  console.log(`${checks} stops and ends walked, ${failed} failures`);
  process.exit(failed ? 1 : 0);
}

main();
