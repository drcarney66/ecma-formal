// wasm_run.mjs MODULE.js ARGS...: runs the Emscripten program MODULE.js (built
// for node with NODERAWFS, build_defs/lean_wasm.bzl) in a Worker whose stack is
// STACK_MB, with ARGS as its arguments, and exits with its status. Its output
// goes straight to file descriptors 1 and 2 (NODERAWFS). A trap (a stack
// overflow) ends the instance: its message goes to stderr and the status is 134.
import { writeSync } from "node:fs";
import { createRequire } from "node:module";
import { resolve } from "node:path";
import { Worker, isMainThread, workerData } from "node:worker_threads";

// tests/run/tail_call_realm.js, the deepest, needs
// more than 384 MB: 256 MB overflows at once, 512 MB runs 300 s (2026-10-15).
const STACK_MB = 1024;

if (isMainThread) {
  const [js, ...args] = process.argv.slice(2);
  const worker = new Worker(new URL(import.meta.url), {
    workerData: resolve(js),
    argv: args,
    resourceLimits: { stackSizeMb: STACK_MB },
  });
  let trapped = false;
  worker.on("error", (e) => {
    trapped = true;
    writeSync(2, `${e instanceof Error ? `${e.name}: ${e.message}` : e}\n`);
  });
  worker.on("exit", (code) => {
    process.exitCode = trapped ? 134 : code;
  });
} else {
  createRequire(import.meta.url)(workerData);
}
