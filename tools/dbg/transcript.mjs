#!/usr/bin/env node
// Runs debugger transcripts against an engine speaking the debugger's protocol
// (lean/Debugger/Protocol.lean: DAP-shaped JSON lines).
//
//   node tools/dbg/transcript.mjs --native BIN FILE.dbg...
//   node tools/dbg/transcript.mjs --wasm-node MJS FILE.dbg...
//   node tools/dbg/transcript.mjs --native-http URL FILE.dbg...
//   node tools/dbg/transcript.mjs --native BIN --trace RUN [--trace-arg ARG]... FILE.js...
//   node tools/dbg/transcript.mjs --native BIN --check-js-stack FILE.js...
//   node tools/dbg/transcript.mjs --wasm-node MJS --suite BUNDLE [--stack-mb N]
//   node tools/dbg/transcript.mjs --native-http URL --suite BUNDLE
//
// A transcript FILE.dbg is tools/dbg/runner.mjs's; "${program}" stands for FILE.js
// next to FILE.dbg.
//
// With --suite, the browser tests' suite (runner.mjs `runSuite`, the bundle
// //:dbg_tests_bundle) runs in node: its result is printed as one JSON line.
// `--stack-mb` sets the Worker's stack (client.mjs's default is 1024), to see what
// a browser's fixed Worker stack allows.
//
// With --trace, each program is stepped in from the entry to its end (`stepIn` at
// every `stopped`), and the `sec-id path.` of each pause must be the suffix of the
// lines `JS_TRACE_STEPS=1 RUN ARG... FILE.js` prints after setup (each ARG a
// `--trace-arg`), and its (reading, path, text) must be a step of its algorithm's
// `specAlgorithm` listing.
//
// With --check-js-stack, each program is stepped in by statements from the entry to
// its end, and at every pause `stackTrace {view: "js"}` must have one frame for each
// context on the execution context stack (`totalFrames` == `contexts`), their spec
// frame ranges adjacent from 0.
//
// The transports: the native engine as a child process (`--native BIN`), its poll
// channel a file; the Worker build (`--wasm-node`, ecma-dbg-web.mjs with its .wasm
// beside it) in a node Worker through tools/dbg/client.mjs, FILE.js written to
// its MEMFS; native ecma-dbg behind `serve.py --engine` at URL (`--native-http`,
// client.mjs's native-http transport), FILE.js sent as the session's program.
// Either way a `pause` request also sets the poll channel.

import { spawn } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, dirname, join, resolve } from "node:path";
import { createInterface } from "node:readline";
import { SessionTransport, Transport, runSuite, runTranscript } from "./runner.mjs";

// The engine as a child process: requests in, messages out; the poll channel a
// file in a directory of its own.
class Native extends Transport {
  constructor(bin, file, extra = []) {
    super();
    this.file = file;
    this.dir = mkdtempSync(join(tmpdir(), "ecma-dbg-"));
    this.poll = join(this.dir, "poll");
    writeFileSync(this.poll, Buffer.from([0]));
    this.proc = spawn(bin, [...extra, "--dbg-poll", this.poll], { stdio: ["pipe", "pipe", "inherit"] });
    this.seq = 1;
    createInterface({ input: this.proc.stdout }).on("line", (line) => this.deliver(line));
    this.exited = new Promise((res) => this.proc.on("close", (code) => {
      this.ended();
      res(code);
    }));
  }

  programPath() {
    return resolve(this.file);
  }

  send(req) {
    if (req.command === "pause") writeFileSync(this.poll, Buffer.from([1]));
    const msg = { seq: this.seq++, type: "request", ...req };
    this.proc.stdin.write(JSON.stringify(msg) + "\n");
    return msg.seq;
  }

  async close() {
    this.proc.stdin.end();
    const t = setTimeout(() => this.proc.kill(), 10000);
    const code = await this.exited;
    clearTimeout(t);
    rmSync(this.dir, { recursive: true, force: true });
    return code;
  }
}

// A session of tools/dbg/client.mjs (a node Worker or native-http), on `file`'s program.
function wasm(client, file) {
  let program = null;
  try {
    program = { name: basename(file), source: readFileSync(file, "utf8") };
  } catch {}
  return new SessionTransport(client, program, (_stream, l) => process.stderr.write(l + "\n"));
}

// The `sec-id path.` lines of the machine's trace after setup's (ecma-run's stderr).
function traceLines(run, traceArgs, program) {
  return new Promise((res, rej) => {
    const p = spawn(run, [...traceArgs, program], {
      stdio: ["ignore", "ignore", "pipe"],
      env: { ...process.env, JS_TRACE_STEPS: "1" },
    });
    const out = [];
    let seen = false;
    createInterface({ input: p.stderr }).on("line", (l) => {
      if (l === "ecma-run: trace") seen = true;
      else if (seen) {
        const [sec, path] = l.split(" ");
        if (path && path.endsWith(".")) out.push(`${sec} ${path}`);
      }
    });
    p.on("close", () => (seen ? res(out) : rej(new Error("no trace mark"))));
  });
}

// A listing's steps, sub-steps after their step: `[reading, path, text]` as JSON.
function listed(steps, out = new Set()) {
  for (const s of steps) {
    out.add(JSON.stringify([s.reading ?? null, s.path, s.text]));
    listed(s.steps ?? [], out);
  }
  return out;
}

async function runTrace(open, run, traceArgs, program) {
  const want = await traceLines(run, traceArgs, resolve(program));
  const eng = open(program);
  const got = [];
  // `specAlgorithm` by secId#idx: the listings, the keys asked in order, each pause's step.
  const listings = new Map();
  const asked = [];
  const stops = [];
  try {
    eng.send({ command: "initialize", arguments: {} });
    eng.send({ command: "launch", arguments: { program: eng.programPath(), stopOnEntry: true } });
    eng.send({ command: "configurationDone" });
    for (;;) {
      const m = await eng.next();
      if (m === null) return "the engine exited before terminated";
      if (m.type === "response" && !m.success) return `${m.command}: ${m.message}`;
      if (m.type === "response" && m.command === "specAlgorithm") listings.set(asked.shift(), listed(m.body.steps));
      if (m.type === "event" && m.event === "stopped") {
        const s = m.body.spec;
        got.push(`${s.reading ?? s.secId} ${s.path}.`);
        const key = `${s.secId}#${s.idx}`;
        if (!listings.has(key) && !asked.includes(key)) {
          asked.push(key);
          eng.send({ command: "specAlgorithm", arguments: { secId: s.secId, idx: s.idx } });
        }
        stops.push({ key, step: JSON.stringify([s.reading ?? null, s.path, s.text]) });
        eng.send({ command: "stepIn" });
      }
      if (m.type === "event" && m.event === "terminated") break;
    }
    eng.send({ command: "disconnect" });
  } finally {
    await eng.close();
  }
  if (got.length === 0) return "no steps";
  const tail = want.slice(want.length - got.length);
  for (let i = 0; i < got.length; i++) {
    if (tail[i] !== got[i]) {
      return `step ${i + 1} of ${got.length}: ${JSON.stringify(got[i])}, the trace has ${JSON.stringify(tail[i])}`;
    }
  }
  for (let i = 0; i < stops.length; i++) {
    const { key, step } = stops[i];
    if (!listings.get(key)?.has(step)) return `step ${i + 1} of ${got.length}: ${step} is not in ${key}'s listing`;
  }
  return `ok: ${got.length} steps of ${want.length}, ${listings.size} listings`;
}

// The JS stack's frames at a pause, against the context count: null if they agree.
function jsStackError(body) {
  const fs = body.stackFrames;
  if (body.totalFrames !== body.contexts) return `${body.totalFrames} JS frames, ${body.contexts} contexts`;
  if (fs.length !== body.totalFrames) return `${fs.length} frames listed of ${body.totalFrames}`;
  let lo = 0;
  for (const f of fs) {
    if (f.spec.frames.lo !== lo || f.spec.frames.hi < lo) return `frame ${f.id} spans ${JSON.stringify(f.spec.frames)}, from ${lo}`;
    lo = f.spec.frames.hi;
  }
  return null;
}

async function runJsStack(open, program) {
  const eng = open(program);
  let stops = 0;
  let where = "";
  const request = async (command, args) => {
    eng.send({ command, arguments: args });
    for (;;) {
      const m = await eng.next();
      if (m === null) throw new Error("the engine exited");
      if (m.type === "response" && m.command === command) {
        if (!m.success) throw new Error(`${command}: ${m.message}`);
        return m.body;
      }
    }
  };
  try {
    eng.send({ command: "initialize", arguments: {} });
    eng.send({ command: "launch", arguments: { program: eng.programPath(), stopOnEntry: true } });
    eng.send({ command: "configurationDone" });
    for (;;) {
      const m = await eng.next();
      if (m === null) return "the engine exited before terminated";
      if (m.type === "response" && !m.success) return `${m.command}: ${m.message}`;
      if (m.type === "event" && m.event === "terminated") break;
      if (m.type === "event" && m.event === "stopped") {
        stops++;
        const js = m.body.js;
        where = js ? `line ${js.line}:${js.column}` : `${m.body.spec.secId} ${m.body.spec.path}`;
        const e = jsStackError(await request("stackTrace", { view: "js" }));
        if (e) return `stop ${stops} (${where}): ${e}`;
        eng.send({ command: "stepIn", arguments: { granularity: "statement" } });
      }
    }
    eng.send({ command: "disconnect" });
  } finally {
    await eng.close();
  }
  return `ok: ${stops} stops`;
}

// The transcript FILE.dbg's program: FILE.js beside it.
const programOf = (file) => join(dirname(file), basename(file, ".dbg") + ".js");

async function main() {
  const args = process.argv.slice(2);
  let bin = null;
  let mjs = null;
  let http = null;
  let run = null;
  const traceArgs = [];
  let suite = null;
  let stackMb = null;
  let jsStack = false;
  const files = [];
  for (let i = 0; i < args.length; i++) {
    if (args[i] === "--native") bin = args[++i];
    else if (args[i] === "--wasm-node") mjs = args[++i];
    else if (args[i] === "--native-http") http = args[++i];
    else if (args[i] === "--trace") run = args[++i];
    else if (args[i] === "--trace-arg") traceArgs.push(args[++i]);
    else if (args[i] === "--suite") suite = args[++i];
    else if (args[i] === "--stack-mb") stackMb = Number(args[++i]);
    else if (args[i] === "--check-js-stack") jsStack = true;
    else files.push(args[i]);
  }
  if ([bin, mjs, http].filter(Boolean).length !== 1 || (files.length === 0) === !suite || (suite && bin) ||
      (jsStack && (run || suite)) || (traceArgs.length > 0 && !run)) {
    console.error("usage: transcript.mjs (--native BIN | --wasm-node MJS | --native-http URL)\n" +
      "         [--trace RUN [--trace-arg ARG]... | --check-js-stack] FILE...\n" +
      "       transcript.mjs (--wasm-node MJS [--stack-mb N] | --native-http URL) --suite BUNDLE");
    process.exit(2);
  }
  let open;
  let client = null;
  if (bin) open = (file) => new Native(bin, file);
  else {
    const { DbgClient } = await import("./client.mjs");
    const t0 = performance.now();
    client = http
      ? DbgClient.connect(http)
      : await DbgClient.load(resolve(mjs).replace(/\.mjs$/, ".wasm"), { glue: resolve(mjs) });
    if (suite) {
      const compileMs = http ? null : Math.round(performance.now() - t0);
      const opts = stackMb ? { stackMb } : {};
      const r = await runSuite(client, JSON.parse(readFileSync(suite, "utf8")), (l) => console.error(l), opts);
      r.timings.compileMs = compileMs;
      console.log(JSON.stringify(r));
      process.exit(r.failed || !r.passed ? 1 : 0);
    }
    open = (file) => wasm(client, file);
  }
  let failed = 0;
  for (const f of files) {
    const text = run || jsStack ? null : readFileSync(f, "utf8");
    let r;
    try {
      r = run ? await runTrace(open, run, traceArgs, f)
        : jsStack ? await runJsStack(open, f)
        : await runTranscript(open(programOf(f)), text);
    } catch (e) {
      r = `error: ${e.message}`;
    }
    const walk = run || jsStack;
    const ok = walk ? r.startsWith("ok") : r === null;
    if (!ok) failed++;
    console.log(ok ? `ok ${f}${walk ? ` (${r.slice(4)})` : ""}` : `FAIL ${f}: ${r}`);
  }
  console.log(`${files.length - failed}/${files.length} passed`);
  process.exit(failed ? 1 : 0);
}

main();
