#!/usr/bin/env node
// The examples' check: every example of a compiled gallery.json (scripts/dbg_gallery.py) run under each
// build it lists, on tools/dbg/ui/model.mjs as the page runs it, against native ecma-dbg (client.mjs's
// native-process transport) or the WebAssembly build in a node Worker. Each must pause where its check
// says and end as it says (gallery.mjs).
//
//   node tools/dbg/ui/gallery_test.mjs --gallery build/gallery.json --builds tools/dbg/builds.json \
//       (--native .lake/build/bin/ecma-dbg [--native-for ID=BIN]... | --wasm-node DIR) [--dump] [--json OUT] [ID...]
//
// With --wasm-node, a build's wasm is DIR/<its wasm> (its .mjs beside it). Natively, the builds whose wasm
// is the first build's run on --native, another only on its --native-for binary (else it is skipped and
// counted). A tour example (`demo`) must have its demo script's breakpoints, filters and lines. --dump prints each pause and end; --explore N pauses N times wherever the run does and checks
// only the end (to write an example's check). --json writes the results: [{id, build, ok, why}].

import { readFileSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { DbgClient } from "../client.mjs";
import { DEMOS } from "../demo/script.mjs";
import { chooseBuild, launchArgs, readBuilds } from "./builds.mjs";
import { printedLines } from "./examples.mjs";
import { endMismatches, pauseMismatches, programOf } from "./gallery.mjs";
import { Model } from "./model.mjs";

const MAX_CONTINUES = 2000;
const paused = (m) => m.state === "paused";
const ended = (m) => m.state === "terminated" || m.state === "ended";
const settled = (m) => paused(m) && m.snap.totalFrames !== null;

async function run(client, build, e, dump, explore = 0) {
  const m = new Model(client, {
    program: programOf(e),
    breakpoints: e.breakpoints ?? [],
    lineBreakpoints: e.lines?.length ? { [e.name]: e.lines.map((line) => ({ line })) } : {},
    filters: e.filters ?? [],
    stopOnEntry: false,
    buildArgs: launchArgs(build, []),
  });
  const want = explore ? { ...e.builds[build.id], pauses: Array(explore).fill({ alg: "?", path: "?" }) } : e.builds[build.id];
  const bad = [];
  m.start();
  try {
    for (const [i, p] of want.pauses.entries()) {
      if (i > 0) m.cont();
      await m.until((m) => settled(m) || ended(m), 120000);
      if (!paused(m)) {
        if (!explore) bad.push(`ended (${m.ending?.outcome ?? m.state}) before pause ${i + 1} at ${p.alg} ${p.path}`);
        break;
      }
      const frames = m.snap.frames.map((f) => f.name);
      if (dump) console.log(JSON.stringify({ id: e.id, build: build.id, pause: i + 1, reason: m.snap.stopped.reason, alg: m.snap.stopped.spec.alg, secId: m.snap.stopped.spec.secId, path: m.snap.stopped.spec.path, frames: frames.slice(0, 10) }));
      if (!explore) bad.push(...pauseMismatches(p, m.snap.stopped, frames).map((w) => `pause ${i + 1}: ${w}`));
    }
    if (!ended(m)) {
      await m.setBreakpoints([]);
      await m.setLineBreakpoints([]);
      await m.setFilters([]);
      for (let k = 0; !ended(m); k++) {
        if (k > MAX_CONTINUES) throw new Error(`still pausing after ${MAX_CONTINUES} continues`);
        if (paused(m)) m.cont();
        await m.until((m) => settled(m) || ended(m), 300000);
      }
    }
    const printed = printedLines(m);
    if (dump) console.log(JSON.stringify({ id: e.id, build: build.id, end: m.ending?.outcome, printed }));
    bad.push(...endMismatches(want, m.ending, printed));
  } catch (err) {
    bad.push(err.message);
  }
  m.stop();
  return bad;
}

async function main() {
  const a = process.argv.slice(2);
  let galleryPath = null;
  let buildsPath = null;
  let native = null;
  let wasmDir = null;
  let dump = false;
  let explore = 0;
  let jsonOut = null;
  const nativeFor = {};
  const only = [];
  for (let i = 0; i < a.length; i++) {
    if (a[i] === "--gallery") galleryPath = a[++i];
    else if (a[i] === "--builds") buildsPath = a[++i];
    else if (a[i] === "--native") native = a[++i];
    else if (a[i] === "--native-for") {
      const [id, bin] = a[++i].split("=");
      nativeFor[id] = bin;
    } else if (a[i] === "--wasm-node") wasmDir = a[++i];
    else if (a[i] === "--dump") dump = true;
    else if (a[i] === "--explore") explore = +a[++i];
    else if (a[i] === "--json") jsonOut = a[++i];
    else only.push(a[i]);
  }
  if (!galleryPath || !buildsPath || !native === !wasmDir) {
    console.error("usage: gallery_test.mjs --gallery FILE --builds FILE (--native BIN [--native-for ID=BIN]... | --wasm-node DIR) [--dump] [--json OUT] [ID...]");
    process.exit(2);
  }
  const gallery = JSON.parse(readFileSync(galleryPath, "utf8"));
  const builds = readBuilds(JSON.parse(readFileSync(buildsPath, "utf8")));
  const clients = new Map();
  const clientFor = async (b) => {
    if (native) {
      const bin = nativeFor[b.id] ?? (b.wasm === builds[0].wasm ? native : null);
      if (!bin) return null;
      if (!clients.has(bin)) clients.set(bin, DbgClient.spawn(bin));
      return clients.get(bin);
    }
    const wasm = resolve(join(wasmDir, b.wasm));
    if (!clients.has(wasm)) clients.set(wasm, await DbgClient.load(wasm, { glue: wasm.replace(/\.wasm$/, ".mjs") }));
    return clients.get(wasm);
  };
  const results = [];
  let failed = 0;
  // A tour example opens with its demo script's configuration (app.mjs): the two must agree.
  for (const e of gallery.examples.filter((x) => x.demo)) {
    const d = DEMOS.find((x) => x.program === e.demo);
    const same = d && ["breakpoints", "filters", "lines"].every((k) => JSON.stringify(d[k] ?? []) === JSON.stringify(e[k] ?? []));
    if (!same) {
      failed++;
      console.log(`FAIL ${e.id}: its breakpoints, filters and lines are not demo/script.mjs's for ${e.demo}`);
    }
  }
  let skipped = 0;
  for (const e of gallery.examples.filter((x) => !only.length || only.includes(x.id))) {
    for (const id of Object.keys(e.builds)) {
      const b = builds.find((x) => x.id === id);
      const client = b && (await clientFor(b));
      if (!client) {
        skipped++;
        console.log(`skip ${e.id} [${id}]: ${b ? "no native binary for this build" : "no such build"}`);
        continue;
      }
      const bad = await run(client, chooseBuild(builds, id), e, dump || explore > 0, explore);
      results.push({ id: e.id, build: id, ok: !bad.length, why: bad });
      if (bad.length) failed++;
      console.log(`${bad.length ? "FAIL" : "ok  "} ${e.id} [${id}]${bad.length ? ": " + bad.join("; ") : ""}`);
    }
  }
  if (jsonOut) writeFileSync(jsonOut, JSON.stringify({ transport: native ? "native" : "wasm-node", results }, null, 1) + "\n");
  console.log(`${results.length} example runs, ${failed} failed, ${skipped} skipped`);
  process.exit(failed ? 1 : 0);
}

main();
