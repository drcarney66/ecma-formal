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
import { chooseBuild, FALLBACK, launchArgs, pageURL, parseArgs, readBuilds, storageKey } from "./builds.mjs";
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
check("builds.json: spec first", table[0].id === "spec" && table[0].args.length === 0, table[0]);
const lit = table.find((b) => b.id === "literal");
check("builds.json: the literal text is the same wasm", lit && lit.wasm === table[0].wasm, lit);
check("builds.json: the literal text reads literally", lit && same(lit.args.slice(0, 2), ["--reading", "literal"]), lit?.args);
check("builds.json: and keeps CreateIntrinsicsAsyncArgument", lit?.args.includes("CreateIntrinsicsAsyncArgument=test262"), lit?.args);
const extra = readBuilds({
  builds: [
    ...table,
    { id: "defer", label: "Proposal: import defer", description: "d", wasm: "ecma-dbg-web-defer.wasm", args: [] },
    { id: "spec", label: "again", wasm: "x.wasm", args: [] },
    { id: "Bad id", wasm: "x.wasm", args: [] },
    { id: "nowasm", args: [] },
    { id: "path", wasm: "../x.wasm", args: [] },
    { id: "args", wasm: "x.wasm", args: "--reading literal" },
  ],
});
check("a build added, the malformed and repeated ones dropped", same(extra.map((b) => b.id), [...table.map((b) => b.id), "defer"]), extra.map((b) => b.id));
check("no build is an error", throws(() => readBuilds({ builds: [] })) && throws(() => readBuilds(null)), "");
check("the fallback is the specification", FALLBACK.length === 1 && FALLBACK[0].id === "spec", FALLBACK);
check("?build= picks its build", chooseBuild(extra, "defer").id === "defer", "");
check("an unknown ?build= is the first", chooseBuild(extra, "nope").id === "spec" && chooseBuild(extra, null).id === "spec", "");

// The arguments, in order.
check("the build's arguments first", same(launchArgs(lit, ["--web-browser"]), [...lit.args, "--web-browser"]), launchArgs(lit, ["--web-browser"]));
check("no arguments", same(launchArgs(table[0], undefined), []), "");
check("?args=", same(parseArgs("--erratum  SortInfiniteComparator=literal --web-browser"), ["--erratum", "SortInfiniteComparator=literal", "--web-browser"]), "");
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
const m = new Model(fake, { program: { name: "a.js", source: "1", args: ["--module"] }, buildArgs: lit.args });
m.start();
const launch = sent.find((x) => x.command === "launch");
check("the model's launch: the build's, then the example's", same(launch?.args.args, [...lit.args, "--module"]), launch);
sent.length = 0;
new Model(fake, { program: { name: "a.js", source: "1" } }).start();
check("the model's launch: none, no args", !("args" in (sent.find((x) => x.command === "launch")?.args ?? {})), sent);

// The configuration per build.
check("storage keys", storageKey("spec") === "ecma-dbg" && storageKey(undefined) === "ecma-dbg" && storageKey("defer") === "ecma-dbg@defer", "");
const st = new MemoryStorage();
saveConfig(st, { breakpoints: [{ alg: "a" }], filters: [], lineBreakpoints: {}, program: null, stopOnEntry: false }, storageKey("spec"));
saveConfig(st, { breakpoints: [{ alg: "b" }], filters: ["stop"], lineBreakpoints: {}, program: null, stopOnEntry: true }, storageKey("defer"));
check("each build its own breakpoints", loadConfig(st, storageKey("spec")).breakpoints[0].alg === "a" && loadConfig(st, storageKey("defer")).breakpoints[0].alg === "b", "");
check("a build with nothing saved", same(loadConfig(st, storageKey("literal")), {}), loadConfig(st, storageKey("literal")));
const old = new MemoryStorage();
old.setItem("esl-dbg-ui", JSON.stringify({ breakpoints: [{ alg: "c" }] }));
check("the old key moves to the specification's", loadConfig(old, storageKey("literal")).breakpoints === undefined && loadConfig(old, storageKey("spec")).breakpoints[0].alg === "c" && old.getItem("esl-dbg-ui") === null, "");

// The page's URL.
const builds = table;
const u = (h, c) => new URL(pageURL(h, c, builds));
check("another build keeps the example", u("https://h/d/?example=demo/get", { build: "literal" }).search === "?example=demo%2Fget&build=literal", u("https://h/d/?example=demo/get", { build: "literal" }).search);
check("the first build leaves the query", u("https://h/d/?example=demo/get&build=literal", { build: "spec" }).search === "?example=demo%2Fget", "");
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

console.log(`${passed} passed, ${failed} failed`);
process.exit(failed ? 1 : 0);
