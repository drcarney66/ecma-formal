#!/usr/bin/env node
// The spec issues' examples (spec-examples.json) on tools/dbg/ui/model.mjs, in node: native ecma-dbg
// as a child process or its WebAssembly build in a node Worker. Each runnable example is started
// with its args and breakpoints, stopped on entry, continued to its report's step (the first stop
// there) where it has a breakpoint, then, with no breakpoint left, to its end: a pause at the
// model's stop where its `stop` filter is on, the end the model's run (examples.mjs). The page's
// side: spectest.mjs.
//
//   node tools/dbg/ui/spec_examples_test.mjs --json spec-examples.json --native .lake/build/bin/ecma-dbg [ID...]
//   node tools/dbg/ui/spec_examples_test.mjs --json spec-examples.json --wasm-node build/web/ecma-dbg-web.mjs

import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { DbgClient } from "../client.mjs";
import { endMismatches, printedLines, stopMismatches } from "./examples.mjs";
import { Model } from "./model.mjs";

const RUN_MS = 600000;
const MAX_STOPS = 3;
const over = (m) => m.state === "terminated" || m.state === "ended";
const pausedAfter = (gen) => (m) => (m.state === "paused" && m.snap.gen > gen) || over(m);

// The example's session: its stops' "reason secId path" and its end's mismatches.
async function walk(client, e) {
  const program = { name: e.name, source: e.source, ...(e.args.length ? { args: e.args } : {}) };
  const m = new Model(client, { program, breakpoints: e.breakpoints, lineBreakpoints: {}, filters: e.filters, stopOnEntry: true });
  const bad = [];
  try {
    m.start();
    await m.until(pausedAfter(0), RUN_MS);
    if (over(m)) return [`ended before its entry: ${m.ending?.outcome ?? m.state}`];
    if (m.snap.stopped.reason !== "entry") bad.push(`the first stop is ${m.snap.stopped.reason}, not entry`);
    let gen = m.snap.gen;
    m.cont();
    if (e.breakpoints.length) {
      const bp = e.breakpoints[0];
      await m.until(pausedAfter(gen), RUN_MS);
      const s = m.snap?.stopped;
      if (!(s?.reason === "breakpoint" && s.spec.secId === bp.alg && s.spec.path === bp.path))
        bad.push(`continue: ${s ? `${s.reason} at ${s.spec.secId} ${s.spec.path}` : m.ending?.outcome}, not ${bp.alg} ${bp.path}`);
      if (!over(m)) {
        await m.setBreakpoints([]);
        gen = m.snap.gen;
        m.cont();
      }
    }
    const stops = [];
    for (;;) {
      await m.until(pausedAfter(gen), RUN_MS);
      if (over(m)) break;
      stops.push(m.snap.stopped);
      if (stops.length > MAX_STOPS) return [...bad, ...stopMismatches(e, stops)];
      gen = m.snap.gen;
      m.cont();
    }
    return [...bad, ...stopMismatches(e, stops), ...endMismatches(e.expect, m.ending, printedLines(m))];
  } finally {
    m.stop();
  }
}

async function main() {
  const args = process.argv.slice(2);
  let json = null;
  let native = null;
  let web = null;
  const only = [];
  for (let i = 0; i < args.length; i++) {
    if (args[i] === "--json") json = args[++i];
    else if (args[i] === "--native") native = args[++i];
    else if (args[i] === "--wasm-node") web = args[++i];
    else only.push(args[i]);
  }
  if (!json || !native === !web) {
    console.error("usage: spec_examples_test.mjs --json spec-examples.json (--native ECMA_DBG | --wasm-node ECMA_DBG_WEB.mjs) [ID...]");
    process.exit(2);
  }
  let client;
  if (native) client = DbgClient.spawn(native);
  else {
    const mjs = resolve(web.endsWith(".mjs") ? web : `${web}.mjs`);
    client = await DbgClient.load(mjs.replace(/\.mjs$/, ".wasm"), { glue: mjs });
  }
  const examples = JSON.parse(readFileSync(json, "utf8")).examples.filter((e) => !only.length || only.includes(e.id));
  let failed = 0;
  let run = 0;
  for (const e of examples) {
    if (e.unrunnable) {
      console.log(`skip ${e.id}: ${e.unrunnable}`);
      continue;
    }
    const t0 = Date.now();
    let bad;
    try {
      bad = e.expect ? await walk(client, e) : ["no model run to compare with"];
    } catch (err) {
      bad = [err.message];
    }
    run++;
    failed += bad.length ? 1 : 0;
    console.log(`${bad.length ? "FAIL" : "ok"} ${e.id} (${((Date.now() - t0) / 1000).toFixed(1)} s)${bad.length ? `: ${bad.join("; ")}` : ""}`);
  }
  console.log(`${run} examples run, ${failed} failed`);
  process.exit(failed || !run ? 1 : 0);
}

main();
