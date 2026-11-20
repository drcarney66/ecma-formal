// The page tools/dbg/test.html: with `?test`, the suite (runner.mjs `runSuite` on
// dbg-tests.json), its progress POSTed to /log and its result to /result
// (tools/dbg/serve.py --test); else a console that sends the protocol's requests
// to a session on the program in the box and logs every message. With `?native`,
// the sessions are the native engine behind serve.py --engine (client.mjs's
// native-http transport), else the WebAssembly build (ecma-dbg-web).

import { DbgClient } from "./client.mjs";
import { runSuite } from "./runner.mjs";

const $ = (id) => document.getElementById(id);
const status = (s) => ($("status").textContent = s);

function log(line) {
  const el = $("log");
  el.textContent += line + "\n";
  el.scrollTop = el.scrollHeight;
}

const post = (path, body) => fetch(path, { method: "POST", body }).catch(() => {});
const params = new URLSearchParams(location.search);
const native = params.has("native");

async function load() {
  if (native) return { client: DbgClient.connect(), compileMs: null };
  const t0 = performance.now();
  const client = await DbgClient.load(new URL("ecma-dbg-web.wasm", location.href));
  return { client, compileMs: Math.round(performance.now() - t0) };
}

async function test() {
  let result;
  try {
    if (!crossOriginIsolated) throw new Error("the page is not cross-origin isolated");
    const { client, compileMs } = await load();
    status(native ? "running the suite on the native engine" : `compiled in ${compileMs} ms; running the suite`);
    const bundle = await (await fetch("dbg-tests.json")).json();
    result = await runSuite(client, bundle, (l) => {
      log(l);
      post("log", l);
    });
    result.timings.compileMs = compileMs;
  } catch (e) {
    result = { passed: 0, failed: 1, failures: [{ name: "page", why: `${e.name}: ${e.message}` }] };
  }
  result.userAgent = navigator.userAgent;
  result.transport = native ? "native-http" : "worker";
  status(`${result.passed} passed, ${result.failed} failed`);
  await post("result", JSON.stringify(result));
}

// The console: one session at a time; a new one restarts on the box's program.
async function console_() {
  const { client, compileMs } = await load();
  status(native ? "native engine" : `compiled in ${compileMs} ms`);
  let s = null;
  const start = () => {
    s?.terminate();
    s = client.session({ name: "program.js", source: $("source").value });
    s.on("message", (m) => log(JSON.stringify(m)));
    s.on("stdout", (l) => log(`stdout: ${l}`));
    s.on("stderr", (l) => log(`stderr: ${l}`));
    s.on("exit", (c) => log(`exit ${c}`));
    s.on("trap", (t) => log(`trap ${t}`));
    log(`session on ${s.program}`);
  };
  const send = (command, args = {}) => {
    if (!s) start();
    s.request(command, args);
  };
  const defaults = {
    launch: () => ({ program: s?.program ?? "", stopOnEntry: true }),
    stackTrace: () => ({ threadId: 1 }),
    pause: () => ({ threadId: 1 }),
  };
  $("start").onclick = start;
  for (const b of document.querySelectorAll("button[data-req]")) {
    const command = b.dataset.req;
    b.onclick = () => {
      if (!s) start();
      send(command, defaults[command]?.() ?? {});
    };
  }
  $("raw").onkeydown = (e) => {
    if (e.key !== "Enter") return;
    try {
      const req = JSON.parse(e.target.value);
      send(req.command, req.arguments ?? {});
    } catch (err) {
      log(`not a request: ${err.message}`);
    }
  };
}

window.addEventListener("error", (e) => log(`error: ${e.message}`));
if (new URLSearchParams(location.search).has("test")) test();
else console_().catch((e) => status(`${e.name}: ${e.message}`));
