#!/usr/bin/env node
// The build selector's logic and the page's other pure parts, in node: the table of builds (builds.mjs),
// the order of a launch's arguments (the build's, then the example's, then `?args=`) as the model sends
// them, the configuration saved per build (breakpoints.mjs), the page's URL for another build, `?args=`,
// the examples' matching (gallery.mjs) and what the page checks of a browser (support.mjs).
//
//   node tools/dbg/ui/builds_test.mjs [--builds tools/dbg/builds.json]

import { readFileSync } from "node:fs";
import { DbgClient } from "../client.mjs";
import { loadConfig, MemoryStorage, saveConfig } from "./breakpoints.mjs";
import { chooseBuild, exampleBuild, FALLBACK, launchArgs, pageURL, parseArgs, readBuilds, storageKey } from "./builds.mjs";
import { endMismatches, findExample, menuGroups, pauseMismatches, programOf, summary } from "./gallery.mjs";
import { Model } from "./model.mjs";
import { missing, MODULES } from "./support.mjs";

let passed = 0;
let failed = 0;
function check(name, ok, got) {
  if (ok) passed++;
  else {
    failed++;
    console.log(`FAIL ${name}: ${JSON.stringify(got)}`);
  }
}
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const throws = (f) => {
  try {
    f();
    return false;
  } catch {
    return true;
  }
};

const i = process.argv.indexOf("--builds");
const file = i > 0 ? process.argv[i + 1] : new URL("../builds.json", import.meta.url);
const table = readBuilds(JSON.parse(readFileSync(file, "utf8")));

// The table.
check("builds.json: spec first", table.length === 1 && table[0].id === "spec" && table[0].args.length === 0, table);
const altBuild = { id: "alt", label: "Alt host", description: "a", wasm: table[0].wasm, args: ["--no-annex-b"] };
const extra = readBuilds({
  builds: [
    ...table,
    altBuild,
    { id: "defer", label: "Proposal: import defer", description: "d", wasm: "ecma-dbg-web-defer.wasm", args: [] },
    { id: "spec", label: "again", wasm: "x.wasm", args: [] },
    { id: "Bad id", wasm: "x.wasm", args: [] },
    { id: "nowasm", args: [] },
    { id: "path", wasm: "../x.wasm", args: [] },
    { id: "args", wasm: "x.wasm", args: "--no-annex-b" },
  ],
});
check("a build added, the malformed and repeated ones dropped", same(extra.map((b) => b.id), ["spec", "alt", "defer"]), extra.map((b) => b.id));
check("no build is an error", throws(() => readBuilds({ builds: [] })) && throws(() => readBuilds(null)), "");
check("the fallback is the specification", FALLBACK.length === 1 && FALLBACK[0].id === "spec", FALLBACK);
check("?build= picks its build", chooseBuild(extra, "defer").id === "defer", "");
check("an unknown ?build= is the first", chooseBuild(extra, "nope").id === "spec" && chooseBuild(extra, null).id === "spec", "");

// The arguments, in order.
check("the build's arguments first", same(launchArgs(altBuild, ["--web-browser"]), ["--no-annex-b", "--web-browser"]), launchArgs(altBuild, ["--web-browser"]));
check("no arguments", same(launchArgs(table[0], undefined), []), "");
check("?args=", same(parseArgs("--no-annex-b  --web-browser"), ["--no-annex-b", "--web-browser"]), "");
check("?args= empty or too long", parseArgs("") === null && parseArgs("   ") === null && parseArgs(Array(40).fill("x").join(" ")) === null, "");
// What the model sends: launch's args are the build's, then the program's.
const sent = [];
const fake = {
  session(program) {
    return {
      program: `work/${program.name}`,
      on() {},
      request(command, args) {
        sent.push({ command, args });
        return new Promise(() => {});
      },
      terminate() {},
    };
  },
};
const m = new Model(fake, { program: { name: "a.js", source: "1", args: ["--module"] }, buildArgs: altBuild.args });
m.start();
const launch = sent.find((x) => x.command === "launch");
check("the model's launch: the build's, then the example's", same(launch?.args.args, ["--no-annex-b", "--module"]), launch);
sent.length = 0;
new Model(fake, { program: { name: "a.js", source: "1" } }).start();
check("the model's launch: none, no args", !("args" in (sent.find((x) => x.command === "launch")?.args ?? {})), sent);

// The configuration per build.
check("storage keys", storageKey("spec") === "ecma-dbg" && storageKey(undefined) === "ecma-dbg" && storageKey("defer") === "ecma-dbg@defer", "");
const st = new MemoryStorage();
saveConfig(st, { breakpoints: [{ alg: "a" }], filters: [], lineBreakpoints: {}, program: null, stopOnEntry: false }, storageKey("spec"));
saveConfig(st, { breakpoints: [{ alg: "b" }], filters: ["stop"], lineBreakpoints: {}, program: null, stopOnEntry: true }, storageKey("defer"));
check("each build its own breakpoints", loadConfig(st, storageKey("spec")).breakpoints[0].alg === "a" && loadConfig(st, storageKey("defer")).breakpoints[0].alg === "b", "");
check("a build with nothing saved", same(loadConfig(st, storageKey("alt")), {}), loadConfig(st, storageKey("alt")));
const old = new MemoryStorage();
old.setItem("esl-dbg-ui", JSON.stringify({ breakpoints: [{ alg: "c" }] }));
check("the old key moves to the specification's", loadConfig(old, storageKey("alt")).breakpoints === undefined && loadConfig(old, storageKey("spec")).breakpoints[0].alg === "c" && old.getItem("esl-dbg-ui") === null, "");

// The page's URL.
const builds = extra;
const u = (h, c) => new URL(pageURL(h, c, builds));
check("another build keeps the example", u("https://h/d/?example=demo/get", { build: "defer" }).search === "?example=demo%2Fget&build=defer", u("https://h/d/?example=demo/get", { build: "defer" }).search);
check("the first build leaves the query", u("https://h/d/?example=demo/get&build=defer", { build: "spec" }).search === "?example=demo%2Fget", "");
check("an example picked drops ?args=", u("https://h/d/?example=a&args=x", { example: "run/b", args: null }).search === "?example=run%2Fb", "");

// The examples' matching.
const g = {
  groups: [{ id: "t", title: "The tour" }, { id: "e", title: "Empty" }],
  examples: [{ id: "demo/get", group: "t", title: "Get", name: "get.js", source: "x", args: ["--module"], builds: { spec: { pauses: [{ alg: "OrdinaryGet", path: "1" }], end: "normal: 8" } } }],
};
check("findExample", findExample(g, "demo/get")?.name === "get.js" && findExample(g, "x") === null && findExample(null, "x") === null, "");
check("programOf", same(programOf(g.examples[0]), { name: "get.js", source: "x", args: ["--module"] }), programOf(g.examples[0]));
check("menuGroups: by title, keyed by id, empty groups left out", same(Object.keys(menuGroups(g)), ["The tour"]) && menuGroups(g)["The tour"][0].key === "demo/get", menuGroups(g));
const stopped = { spec: { alg: "OrdinaryGet", secId: "sec-ordinaryget", path: "1" } };
check("a pause by name", pauseMismatches({ alg: "OrdinaryGet", path: "1" }, stopped, []).length === 0, "");
check("a pause by sec-id", pauseMismatches({ alg: "sec-ordinaryget", path: "1" }, stopped, []).length === 0, "");
check("a pause at another step", pauseMismatches({ alg: "OrdinaryGet", path: "2" }, stopped, []).length === 1, "");
check("frames in order, gaps allowed", pauseMismatches({ alg: "OrdinaryGet", path: "1", frames: ["OrdinaryGet", "GetValue"] }, stopped, ["OrdinaryGet", "[[Get]]", "GetValue"]).length === 0, "");
check("frames out of order", pauseMismatches({ alg: "OrdinaryGet", path: "1", frames: ["GetValue", "OrdinaryGet"] }, stopped, ["OrdinaryGet", "[[Get]]", "GetValue"]).length === 1, "");
check("an end", endMismatches({ end: "normal: 8" }, { outcome: "normal: 8", exitCode: 0 }, []).length === 0, "");
check("an end with an object's number", endMismatches({ end: "normal: [object #N]" }, { outcome: "normal: [object #20472]", exitCode: 0 }, []).length === 0, "");
check("a stop's step left open", endMismatches({ end: "stop: sortError sec-x#0 ?" }, { outcome: "stop: sortError sec-x#0 4.a", exitCode: 3 }, []).length === 0, "");
check("printed lines compared", endMismatches({ end: "normal: 8", printed: ["a"] }, { outcome: "normal: 8" }, ["b"]).length === 1, "");
check("summary", summary(g.examples[0].builds.spec) === "pauses at OrdinaryGet 1; ends normal: 8", summary(g.examples[0].builds.spec));

// What the page checks of a browser.
const full = { WebAssembly, Worker: function () {}, SharedArrayBuffer, Atomics, isSecureContext: true };
check("node has all of it", same(missing(full), []), missing(full));
check("no WebAssembly", same(missing({ ...full, WebAssembly: undefined }), ["WebAssembly"]), "");
const noMem64 = { validate: (b) => b !== MODULES.MEMORY64 && WebAssembly.validate(b) };
check("no Memory64", same(missing({ ...full, WebAssembly: noMem64 }), ["WebAssembly's 64-bit memory (Memory64)"]), missing({ ...full, WebAssembly: noMem64 }));
check("no workers, no Atomics.wait", missing({ ...full, Worker: undefined, Atomics: {} }).length === 2, missing({ ...full, Worker: undefined, Atomics: {} }));
for (const [k, b] of Object.entries(MODULES)) check(`the ${k} probe is valid wasm`, WebAssembly.validate(b), k);
const broken = new Uint8Array(MODULES.MEMORY64);
broken[broken.length - 2] = 0x08;
check("a malformed probe is not", !WebAssembly.validate(broken), "");

// Lazy WASM loading: zero compilation until ensureLoaded()/session(), then cached.
let compiles = 0;
const fakeMod = await WebAssembly.compile(MODULES.MEMORY64);
const lazy = DbgClient.lazy("https://example.invalid/ecma-dbg-web-prop.wasm", {
  compile: async () => {
    compiles++;
    return fakeMod;
  },
});
check("lazy client compiles nothing upfront", compiles === 0 && lazy.module === null && lazy.transport === "worker", compiles);
const loaded1 = await lazy.ensureLoaded();
const loaded2 = await lazy.ensureLoaded();
check("lazy client compiles once on demand and caches glue", compiles === 1 && loaded1.module === fakeMod && loaded2.module === fakeMod && loaded1.glue.endsWith("ecma-dbg-web-prop.mjs"), { compiles, glue: loaded1.glue });

// Auto-selecting a proposal example's primary build when picked from the menu.
const popBuild = readBuilds({ builds: [{ id: "popcount", label: "Proposal: popcount", description: "p", wasm: "ecma-dbg-web-popcount.wasm", wasmBytes: 13185591, args: [] }] })[0];
const allBuilds = [...extra, popBuild];
check("builds.json: preserves optional wasmBytes", popBuild.wasmBytes === 13185591 && !("wasmBytes" in extra[0]), popBuild);
const popEx = { id: "dbg/proposal_popcount", builds: { popcount: { pauses: [], end: "normal: undefined" }, spec: { pauses: [], end: "throw: TypeError" } } };
const errataEx = { id: "run/module_top_level_await", builds: { spec: { pauses: [], end: "normal: undefined" }, alt: { pauses: [], end: "stop: ?" } } };
const specOnlyEx = { id: "demo/get", builds: { spec: { pauses: [], end: "normal: 8" } } };
check("picking popcount on spec switches to popcount", exampleBuild(popEx, allBuilds[0], allBuilds).id === "popcount", "");
check("picking popcount on defer switches to popcount", exampleBuild(popEx, chooseBuild(allBuilds, "defer"), allBuilds).id === "popcount", "");
check("picking shared example on alt keeps alt", exampleBuild(errataEx, altBuild, allBuilds).id === "alt", "");
check("picking spec-only example on popcount switches back to spec", exampleBuild(specOnlyEx, popBuild, allBuilds).id === "spec", "");
const states = [];
const versionedLazy = DbgClient.lazy("https://example.invalid/ecma-dbg-web-popcount.wasm?v=abc", {
  expectedBytes: 1000,
  compile: async (_u, opts) => {
    opts?.onProgress?.({ loaded: 500, total: 1000, phase: "downloading" });
    opts?.onProgress?.({ loaded: 1000, total: 1000, phase: "compiling" });
    return fakeMod;
  },
});
versionedLazy.onLoadState = (st, info) => states.push({ st, phase: info?.phase ?? null, loaded: info?.loaded ?? null });
const loadedVer = await versionedLazy.ensureLoaded();
check("lazy client preserves version query on glue URL", loadedVer.glue === "https://example.invalid/ecma-dbg-web-popcount.mjs?v=abc", loadedVer.glue);
check("lazy client emits loading, progress, and ready states", states.length === 4 && states[0].st === "loading" && states[1].loaded === 500 && states[2].phase === "compiling" && states[3].st === "ready", states);

console.log(`${passed} passed, ${failed} failed`);
process.exit(failed ? 1 : 0);
