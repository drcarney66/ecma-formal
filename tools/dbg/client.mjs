// The debugger's client, on one of three transports, with the same API:
// - "worker": a Worker build of the debugger run in a Worker
//   (tools/dbg/engine-worker.mjs), one per session: ecma-dbg's (ecma-dbg-web,
//   scripts/build_wasm.py). The same module works in a
//   browser (a module Worker; the page must be cross-origin isolated for
//   SharedArrayBuffer) and in node (`worker_threads`).
// - "native-http": native ecma-dbg, one process per session, spawned by
//   tools/dbg/serve.py --engine: requests are POSTed in order, messages come
//   back as Server-Sent Events (read through fetch, so node can use it too).
// - "native-process" (node only): native ecma-dbg as a child process, one per
//   session, as serve.py runs it (the program in work/NAME of its directory).
//
//   const dbg = await DbgClient.load("ecma-dbg-web.wasm");  // or its bytes, {glue}
//   const dbg = DbgClient.connect("http://127.0.0.1:PORT/"); // native-http
//   const dbg = DbgClient.spawn(".lake/build/bin/ecma-dbg");  // native-process
//   const s = dbg.session({ name: "a.js", source }, { argv: [] });
//   s.on("stopped", (body) => ...);
//   await s.request("initialize");
//   await s.request("launch", { program: s.program, stopOnEntry: true });
//
// `request(command, args)` resolves with the engine's response (success or not).
// `on(name, fn)` takes an event's body for an engine event (`stopped`, `output`,
// `terminated`, ...), every engine message for "message", and the engine's end
// for "exit" (status) and "trap" ("Name: message"); "stdout" and "stderr" take
// lines the engine printed. `pause()` sets the pause flag (the poll channel),
// which the engine polls while it runs; a `pause` request sets it too, and the
// engine answers it at the pause, after `stopped`. `close()` ends the engine's
// input, `terminate()` the engine. A restart is a new session: the compiled
// module is reused.

import { PROGRAM_DIR, RingWriter, newRing } from "./ring.mjs";

const wt = typeof Worker === "undefined" ? await import("node:worker_threads") : null;
const node = wt && {
  child: await import("node:child_process"),
  fs: await import("node:fs"),
  os: await import("node:os"),
  path: await import("node:path"),
  readline: await import("node:readline"),
};

// A string with no URL scheme is a file path in node.
async function toURL(u) {
  if (u instanceof URL) return u;
  if (wt && !/^[a-z][a-z0-9+.-]*:/i.test(u)) {
    const { pathToFileURL } = await import("node:url");
    return pathToFileURL(u);
  }
  return new URL(u, globalThis.location?.href);
}

async function fetchBytes(url) {
  if (url.protocol === "file:") {
    const { readFile } = await import("node:fs/promises");
    return readFile(url);
  }
  const r = await fetch(url);
  if (!r.ok) throw new Error(`${url}: ${r.status} ${r.statusText}`);
  return new Uint8Array(await r.arrayBuffer());
}

// Compiled WebAssembly.Modules keyed by URL href, so lazy clients share and reuse compilations.
const compiledModules = new Map();

async function compileWasmURL(url) {
  const key = url.href;
  if (!compiledModules.has(key)) {
    const p = (async () => {
      if (url.protocol !== "file:" && typeof WebAssembly.compileStreaming === "function") {
        try {
          const resp = await fetch(url);
          if (!resp.ok) throw new Error(`${url}: ${resp.status} ${resp.statusText}`);
          const ct = resp.headers.get("content-type") ?? "";
          if (ct.includes("application/wasm")) return await WebAssembly.compileStreaming(resp);
          return await WebAssembly.compile(new Uint8Array(await resp.arrayBuffer()));
        } catch (e) {
          compiledModules.delete(key);
          throw e;
        }
      }
      try {
        return await WebAssembly.compile(await fetchBytes(url));
      } catch (e) {
        compiledModules.delete(key);
        throw e;
      }
    })();
    compiledModules.set(key, p);
  }
  return compiledModules.get(key);
}

export class DbgClient {
  constructor(module, glue, server = null, bin = null, loader = null) {
    this.module = module;
    this.glue = glue;
    this.server = server;
    this.bin = bin;
    this.loader = loader;
    this.loading = false;
    this.onLoadState = null;
    this.transport = server ? "native-http" : bin ? "native-process" : "worker";
  }

  // The native-process transport (node only): `bin` is native ecma-dbg.
  static spawn(bin) {
    if (!node) throw new Error("native-process: node only");
    return new DbgClient(null, null, null, node.path.resolve(bin));
  }

  // The native-http transport: `server` is serve.py's base URL (by default the
  // page's directory).
  static connect(server = new URL(".", globalThis.location?.href)) {
    const url = new URL(server);
    if (!url.pathname.endsWith("/")) url.pathname += "/";
    return new DbgClient(null, null, url);
  }

  // Compiles the engine once: `wasm` is NAME.wasm's URL (or path, in node) or its
  // bytes; `glue` is NAME.mjs's, by default next to the wasm.
  static async load(wasm, { glue } = {}) {
    if (typeof wasm === "string" || wasm instanceof URL) {
      const wasmURL = await toURL(wasm);
      const glueURL = glue ? await toURL(glue) : new URL(wasmURL.href.replace(/\.wasm(?=$|\?)/, ".mjs"));
      return new DbgClient(await compileWasmURL(wasmURL), glueURL.href);
    }
    if (!glue) throw new Error("DbgClient.load: bytes need {glue}");
    const glueURL = await toURL(glue);
    return new DbgClient(await WebAssembly.compile(wasm), glueURL.href);
  }

  // Lazy Worker client: fetches and compiles `wasm` only on the first `session()` call
  // (or `ensureLoaded()`), reusing `compiledModules` across restarts and build switches.
  static lazy(wasm, { glue, compile = compileWasmURL } = {}) {
    let promise = null;
    const client = new DbgClient(null, null, null, null, async () => {
      if (client.module) return { module: client.module, glue: client.glue };
      if (!promise) {
        client.loading = true;
        client.onLoadState?.("loading");
        promise = (async () => {
          const wasmURL = await toURL(wasm);
          const glueURL = glue ? await toURL(glue) : new URL(wasmURL.href.replace(/\.wasm(?=$|\?)/, ".mjs"));
          const mod = await compile(wasmURL);
          client.module = mod;
          client.glue = glueURL.href;
          return { module: mod, glue: glueURL.href };
        })().finally(() => {
          client.loading = false;
          client.onLoadState?.("ready");
        });
        promise.catch(() => {
          promise = null;
        });
      }
      return promise;
    });
    return client;
  }

  async ensureLoaded() {
    if (this.module) return { module: this.module, glue: this.glue };
    if (!this.loader) throw new Error("DbgClient: no module or loader");
    return this.loader();
  }

  // A session on `program` ({name, source}, or null), in a new Worker or engine.
  // `opts.argv` are more ecma-dbg arguments (Worker only); `opts.stackMb` the node
  // Worker's stack (a browser Worker's cannot be set).
  session(program, opts = {}) {
    if (this.bin) return new ProcessSession(this, program, opts);
    return this.server ? new HttpSession(this, program, opts) : new DbgSession(this, program, opts);
  }
}

// What both transports share: listeners, the pending requests and the engine's lines.
class Session {
  constructor(program) {
    this.program = program;
    this.seq = 1;
    this.pending = new Map();
    this.listeners = new Map();
    this.ended = false;
  }

  emit(name, value) {
    for (const fn of this.listeners.get(name) ?? []) fn(value);
  }

  on(name, fn) {
    if (!this.listeners.has(name)) this.listeners.set(name, []);
    this.listeners.get(name).push(fn);
    return this;
  }

  // One line the engine wrote on its protocol channel.
  line(text) {
    let msg;
    try {
      msg = JSON.parse(text);
    } catch {
      msg = { unparsed: text };
    }
    this.emit("message", msg);
    if (msg.type === "response") {
      const p = this.pending.get(msg.request_seq);
      if (p) {
        this.pending.delete(msg.request_seq);
        p(msg);
      }
    } else if (msg.type === "event") this.emit(msg.event, msg.body);
  }

  // The engine's end: {exit: status} or {trap: "Name: message"}.
  finish(m) {
    if (this.ended) return;
    this.end();
    if ("exit" in m) this.emit("exit", m.exit);
    else this.emit("trap", m.trap);
  }

  // A new request: its message, and the promise of its response.
  newRequest(command, args) {
    const seq = this.seq++;
    const reply = new Promise((res) => this.pending.set(seq, res));
    return [{ seq, type: "request", command, arguments: args }, reply];
  }

  settle() {
    this.ended = true;
    for (const p of this.pending.values()) p(null);
    this.pending.clear();
  }

  terminate() {
    this.end();
  }
}

// tests/run/tail_call_realm.js needs more than 384 MB of stack under node
// (transcript.mjs --wasm-node).
const STACK_MB = 1024;

export class DbgSession extends Session {
  constructor(client, program, { argv = [], stackMb = STACK_MB } = {}) {
    super(program ? `${PROGRAM_DIR}/${program.name}` : null);
    const sab = newRing();
    this.ring = new RingWriter(sab);
    this.encoder = new TextEncoder();
    this.worker = null;
    const startWorker = (module, glue) => {
      if (this.ended) return;
      const url = new URL("./engine-worker.mjs", import.meta.url);
      if (wt) {
        this.worker = new wt.Worker(url, { resourceLimits: { stackSizeMb: stackMb } });
        this.worker.on("message", (m) => this.fromWorker(m));
        this.worker.on("error", (e) => this.fromWorker({ trap: `${e.name}: ${e.message}` }));
      } else {
        this.worker = new Worker(url, { type: "module" });
        this.worker.onmessage = (e) => this.fromWorker(e.data);
        this.worker.onerror = (e) => this.fromWorker({ trap: `Error: ${e.message}` });
      }
      this.worker.postMessage({ type: "start", glue, module, sab, program, argv });
    };
    if (client.module) {
      startWorker(client.module, client.glue);
    } else {
      client.ensureLoaded().then(
        ({ module, glue }) => startWorker(module, glue),
        (e) => this.fromWorker({ trap: e instanceof Error ? `${e.name}: ${e.message}` : String(e) }),
      );
    }
  }

  fromWorker(m) {
    if ("line" in m) this.line(m.line);
    else if ("stdout" in m) this.emit("stdout", m.stdout);
    else if ("stderr" in m) this.emit("stderr", m.stderr);
    else if ("exit" in m || "trap" in m) this.finish(m);
  }

  // Sends a request; resolves with its response (null if the engine ends first).
  request(command, args = {}) {
    if (this.ended) return Promise.resolve(null);
    if (command === "pause") this.pause();
    const [msg, reply] = this.newRequest(command, args);
    this.ring.write(this.encoder.encode(JSON.stringify(msg) + "\n"));
    return reply;
  }

  pause() {
    this.ring.setPause(1);
  }

  // The end of the input: the engine ends as at the end of stdin.
  close() {
    this.ring.close();
  }

  end() {
    if (this.ended) return;
    this.settle();
    if (this.worker) this.worker.terminate();
  }
}

// A native ecma-dbg behind serve.py (`POST /session`). The program is written to
// work/NAME in the engine's own directory, its working directory. Requests are
// POSTed one after another, so that they reach the engine in order; serve.py sets
// the poll file for a `pause` request.
export class HttpSession extends Session {
  constructor(client, program, { argv = [] } = {}) {
    super(program ? `work/${program.name}` : null);
    if (argv.length) throw new Error("native-http: ecma-dbg takes no more arguments");
    this.server = client.server;
    this.abort = new AbortController();
    this.id = null;
    // Not aborted by end(): a session ended while it is made is deleted once made.
    this.created = this.post("session", { program }, null).then(async (r) => {
      this.id = (await r.json()).id;
      if (this.ended) this.delete();
      else this.listen().catch((e) => this.fail(e));
    });
    this.chain = this.created;
    this.chain.catch((e) => this.fail(e));
  }

  async post(path, body, signal = this.abort.signal) {
    const r = await fetch(new URL(path, this.server), {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: body === undefined ? "" : JSON.stringify(body),
      signal,
    });
    if (!r.ok) throw new Error(`POST /${path}: ${r.status} ${(await r.text()).trim()}`);
    return r;
  }

  // `path` under the session (POSTed after the earlier ones).
  enqueue(path, body) {
    this.chain = this.chain.then(() => (this.ended ? null : this.post(`session/${this.id}${path}`, body)));
    this.chain.catch((e) => this.fail(e));
  }

  // The engine's messages (`data`), stderr lines and exit status, until its exit.
  async listen() {
    const r = await fetch(new URL(`session/${this.id}/events`, this.server), {
      headers: { Accept: "text/event-stream" },
      signal: this.abort.signal,
    });
    if (!r.ok) throw new Error(`GET events: ${r.status}`);
    const reader = r.body.pipeThrough(new TextDecoderStream()).getReader();
    let buf = "";
    for (;;) {
      const { value, done } = await reader.read();
      if (done) break;
      buf += value;
      for (let i; (i = buf.indexOf("\n\n")) >= 0; ) {
        this.event(buf.slice(0, i));
        buf = buf.slice(i + 2);
      }
    }
    this.fail(new Error("the server ended the session's events"));
  }

  // One Server-Sent Event: its `event` (default "message") and `data` fields.
  event(block) {
    let name = "message";
    const data = [];
    for (const l of block.split("\n")) {
      if (l.startsWith(":")) continue;
      const c = l.indexOf(":");
      const field = c < 0 ? l : l.slice(0, c);
      const value = c < 0 ? "" : l.slice(c + 1).replace(/^ /, "");
      if (field === "event") name = value;
      else if (field === "data") data.push(value);
    }
    if (!data.length) return;
    const text = data.join("\n");
    if (name === "message") this.line(text);
    else if (name === "stderr") this.emit("stderr", text);
    else if (name === "exit") this.finish({ exit: Number(text) });
  }

  fail(e) {
    if (!this.ended) this.finish({ trap: `${e.name}: ${e.message}` });
  }

  // Sends a request; resolves with its response (null if the engine ends first).
  request(command, args = {}) {
    if (this.ended) return Promise.resolve(null);
    const [msg, reply] = this.newRequest(command, args);
    this.enqueue("", msg);
    return reply;
  }

  pause() {
    this.created.then(() => this.ended || this.post(`session/${this.id}/pause`)).catch((e) => this.fail(e));
  }

  close() {
    this.enqueue("/close");
  }

  delete() {
    fetch(new URL(`session/${this.id}`, this.server), { method: "DELETE" }).catch(() => {});
  }

  end() {
    if (this.ended) return;
    this.settle();
    this.abort.abort();
    if (this.id) this.delete();
  }
}

// Native ecma-dbg as a child process in a new directory, its working directory: the
// program written to work/NAME there, the poll channel the file `poll`.
export class ProcessSession extends Session {
  constructor(client, program, { argv = [] } = {}) {
    super(program ? `work/${program.name}` : null);
    if (argv.length) throw new Error("native-process: ecma-dbg takes no more arguments");
    const { child, fs, os, path, readline } = node;
    this.dir = fs.mkdtempSync(path.join(os.tmpdir(), "ecma-dbg-"));
    this.poll = path.join(this.dir, "poll");
    fs.writeFileSync(this.poll, Buffer.from([0]));
    if (program) {
      fs.mkdirSync(path.join(this.dir, "work"));
      fs.writeFileSync(path.join(this.dir, this.program), program.source);
    }
    this.proc = child.spawn(client.bin, ["--dbg-poll", this.poll], { cwd: this.dir, stdio: ["pipe", "pipe", "pipe"] });
    readline.createInterface({ input: this.proc.stdout }).on("line", (l) => this.line(l));
    readline.createInterface({ input: this.proc.stderr }).on("line", (l) => this.emit("stderr", l));
    this.proc.stdin.on("error", () => {});
    this.proc.on("error", (e) => this.finish({ trap: `${e.name}: ${e.message}` }));
    this.proc.on("close", (code, signal) => {
      fs.rmSync(this.dir, { recursive: true, force: true });
      this.finish({ exit: code ?? 128 + (os.constants.signals[signal] ?? 0) });
    });
  }

  // Sends a request; resolves with its response (null if the engine ends first).
  request(command, args = {}) {
    if (this.ended) return Promise.resolve(null);
    if (command === "pause") this.pause();
    const [msg, reply] = this.newRequest(command, args);
    this.proc.stdin.write(JSON.stringify(msg) + "\n");
    return reply;
  }

  pause() {
    if (!this.ended) node.fs.writeFileSync(this.poll, Buffer.from([1]));
  }

  close() {
    this.proc.stdin.end();
  }

  end() {
    if (this.ended) return;
    this.settle();
    if (this.proc.exitCode === null && this.proc.signalCode === null) this.proc.kill();
  }
}
