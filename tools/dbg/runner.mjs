// The debugger tests' core, shared by tools/dbg/transcript.mjs (node) and the page
// tools/dbg/test.mjs (a browser): transcripts, programs run to their end, and the
// suite of both with its timings. No node or DOM imports.
//
// A transcript is JSON lines, `//` lines and blank lines aside:
//   {"send": REQUEST}   a request; `seq` and `"type": "request"` are filled in
//   {"expect": MESSAGE} the engine's next message, matched as a subset: an object's
//                       fields recursively, an array's first elements, else equal;
//                       with a "..." element, the ones after it match later elements in
//                       order, gaps allowed
//   {"sleep": MS}       a wait
// The string "${program}" anywhere stands for the transcript's program.
// In an expected message, the string "${=NAME}" matches any value and binds NAME to
// it; later, the string "${NAME}" (the whole string) stands for that value, in a
// request or in an expected message (a variablesReference, a value shown). Inside a
// longer expected string, "${=NAME}" matches some text and binds NAME to it, and
// "${NAME}" stands for its value's text ("normal: [object ${o}]", a heap address).
//
// The suite's bundle (scripts/dbg_browser_bundle.py):
//   transcripts  [{name, dbg, program: {name, source} | null}]
//   programs     [{name, source, depth?, stdout, outcome, exitCode, nativeMs}], the
//                outcomes of native `ecma-run`

export const TIMEOUT_MS = 300000;

const now = () => performance.now();

// An engine's messages, in order: `next()` waits for one.
export class Transport {
  constructor() {
    this.queue = [];
    this.waiters = [];
    this.closed = false;
  }

  deliver(line) {
    let msg;
    try {
      msg = JSON.parse(line);
    } catch {
      msg = { unparsed: line };
    }
    this.deliverMessage(msg);
  }

  deliverMessage(msg) {
    const w = this.waiters.shift();
    if (w) w.resolve(msg);
    else this.queue.push(msg);
  }

  ended() {
    this.closed = true;
    for (const w of this.waiters.splice(0)) w.resolve(null);
  }

  // The next message, or null when the engine has exited.
  next(timeoutMs = TIMEOUT_MS) {
    if (this.queue.length) return Promise.resolve(this.queue.shift());
    if (this.closed) return Promise.resolve(null);
    return new Promise((res, rej) => {
      const w = { resolve: (m) => { clearTimeout(t); res(m); } };
      const t = setTimeout(() => {
        this.waiters.splice(this.waiters.indexOf(w), 1);
        rej(new Error(`no message within ${timeoutMs / 1000} s`));
      }, timeoutMs);
      this.waiters.push(w);
    });
  }
}

// A Worker session of tools/dbg/client.mjs on `program` ({name, source} or null),
// with the session options `opts`. `onText(stream, line)` takes what the engine
// printed; `trap` is the Worker's trap ("Name: message"), if it had one.
export class SessionTransport extends Transport {
  constructor(client, program, onText = () => {}, opts = {}) {
    super();
    this.trap = null;
    this.session = client.session(program, opts);
    this.session.on("message", (m) => this.deliverMessage(m));
    this.session.on("stderr", (l) => onText("stderr", l));
    this.session.on("stdout", (l) => onText("stdout", l));
    this.exited = new Promise((res) => {
      this.session.on("exit", (code) => {
        this.ended();
        res(code);
      });
      this.session.on("trap", (t) => {
        this.trap = t;
        onText("stderr", `engine trap: ${t}`);
        this.ended();
        res(134);
      });
    });
  }

  programPath() {
    return this.session.program;
  }

  send(req) {
    this.session.request(req.command, req.arguments ?? {});
  }

  async close() {
    this.session.close();
    const t = setTimeout(() => this.session.terminate(), 10000);
    return this.exited.finally(() => clearTimeout(t));
  }
}

// Where `got` differs from the subset `exp`: a description, or null. A
// "${=NAME}" binds NAME in `vars` to what it meets.
export function mismatch(exp, got, vars = {}, at = "") {
  const bind = typeof exp === "string" && /^\$\{=(\w+)\}$/.exec(exp);
  if (bind) {
    if (got === undefined) return `${at || "."}: missing, expected a value for ${bind[1]}`;
    vars[bind[1]] = got;
    return null;
  }
  const use = typeof exp === "string" && /^\$\{(\w+)\}$/.exec(exp);
  if (use && use[1] !== "program") {
    if (!(use[1] in vars)) return `${at || "."}: \${${use[1]}} is not bound`;
    const want = JSON.stringify(vars[use[1]]);
    return JSON.stringify(got) === want ? null : `${at || "."}: ${JSON.stringify(got)}, expected ${want}`;
  }
  if (typeof exp === "string" && /\$\{=?\w+\}/.test(exp)) return template(exp, got, vars, at);
  if (exp !== null && typeof exp === "object") {
    if (Array.isArray(exp)) {
      if (!Array.isArray(got)) return `${at || "."}: expected an array`;
      const gap = exp.indexOf("...");
      if (gap >= 0) {
        if (got.length < gap) return `${at || "."}: ${got.length} elements, expected at least ${gap}`;
        for (let i = 0; i < gap; i++) {
          const m = mismatch(exp[i], got[i], vars, `${at}[${i}]`);
          if (m) return m;
        }
        let j = gap;
        for (let i = gap + 1; i < exp.length; i++) {
          let found = false;
          for (; j < got.length && !found; j++) {
            const tried = { ...vars };
            if (!mismatch(exp[i], got[j], tried, `${at}[${j}]`)) {
              Object.assign(vars, tried);
              found = true;
            }
          }
          if (!found) return `${at || "."}: no element after the earlier ones matches ${JSON.stringify(exp[i])}`;
        }
        return null;
      }
      if (got.length < exp.length) return `${at || "."}: ${got.length} elements, expected at least ${exp.length}`;
      for (let i = 0; i < exp.length; i++) {
        const m = mismatch(exp[i], got[i], vars, `${at}[${i}]`);
        if (m) return m;
      }
      return null;
    }
    if (got === null || typeof got !== "object" || Array.isArray(got)) return `${at || "."}: expected an object`;
    for (const k of Object.keys(exp)) {
      const m = mismatch(exp[k], got[k], vars, `${at}.${k}`);
      if (m) return m;
    }
    return null;
  }
  return exp === got ? null : `${at || "."}: ${JSON.stringify(got)}, expected ${JSON.stringify(exp)}`;
}

// Where `got` differs from the string `exp` with "${=NAME}" and "${NAME}" inside it.
function template(exp, got, vars, at) {
  if (typeof got !== "string") return `${at || "."}: ${JSON.stringify(got)}, expected a string like ${JSON.stringify(exp)}`;
  const names = [];
  let re = "";
  for (const part of exp.split(/(\$\{=?\w+\})/)) {
    const m = /^\$\{(=?)(\w+)\}$/.exec(part);
    if (!m) re += part.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    else if (m[1]) {
      names.push(m[2]);
      re += "(.+?)";
    } else if (!(m[2] in vars)) return `${at || "."}: \${${m[2]}} is not bound`;
    else re += String(vars[m[2]]).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  }
  const m = new RegExp(`^${re}$`, "s").exec(got);
  if (!m) return `${at || "."}: ${JSON.stringify(got)}, expected ${JSON.stringify(exp)}`;
  names.forEach((n, i) => (vars[n] = m[i + 1]));
  return null;
}

// In an expect (`late`), a "${NAME}" is left for `mismatch`, so that it may use a binding
// made earlier in the same message.
export function substitute(v, program, vars = {}, late = false) {
  if (typeof v === "string") {
    const use = /^\$\{(\w+)\}$/.exec(v);
    if (use && use[1] !== "program") {
      if (late) return v;
      if (!(use[1] in vars)) throw new Error(`\${${use[1]}} is not bound`);
      return vars[use[1]];
    }
    return v.split("${program}").join(program);
  }
  if (Array.isArray(v)) return v.map((x) => substitute(x, program, vars, late));
  if (v !== null && typeof v === "object") {
    return Object.fromEntries(Object.entries(v).map(([k, x]) => [k, substitute(x, program, vars, late)]));
  }
  return v;
}

export const sleep = (ms) => new Promise((res) => setTimeout(res, ms));

// Runs the transcript `text` on the engine `eng` (a Transport with send,
// programPath and close): null, or where it failed.
export async function runTranscript(eng, text) {
  const program = eng.programPath();
  const lines = text.split("\n");
  const vars = {};
  try {
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i].trim();
      if (!line || line.startsWith("//")) continue;
      let entry;
      try {
        const raw = JSON.parse(line);
        entry = substitute(raw, program, vars, raw.expect !== undefined);
      } catch (e) {
        return `line ${i + 1}: ${e.message}`;
      }
      if (entry.send) eng.send(entry.send);
      else if (entry.sleep) await sleep(entry.sleep);
      else if (entry.expect) {
        const got = await eng.next();
        if (got === null) return `line ${i + 1}: the engine exited${eng.trap ? ` (${eng.trap})` : ""}`;
        const m = mismatch(entry.expect, got, vars);
        if (m) return `line ${i + 1}: ${m}\n  got ${JSON.stringify(got).slice(0, 2000)}`;
      } else return `line ${i + 1}: neither send nor expect`;
    }
    return null;
  } finally {
    await eng.close();
  }
}

// Runs `prog` (a bundle program) by `continue` to its end and compares its output,
// outcome and status with native ecma-run's: {ok, ms, why?, trap?}. `ms` is from
// `configurationDone` to `terminated`.
export async function runProgram(client, prog, opts = {}) {
  const eng = new SessionTransport(client, { name: prog.name, source: prog.source }, undefined, opts);
  let out = "";
  let t0 = 0;
  try {
    eng.send({ command: "initialize" });
    eng.send({ command: "launch", arguments: { program: eng.programPath() } });
    t0 = now();
    eng.send({ command: "configurationDone" });
    for (;;) {
      const m = await eng.next();
      if (m === null) return { ok: false, ms: now() - t0, why: "the engine exited", trap: eng.trap };
      if (m.type === "response" && !m.success) return { ok: false, ms: now() - t0, why: `${m.command}: ${m.message}` };
      if (m.type === "event" && m.event === "output" && m.body.category === "stdout") out += m.body.output;
      if (m.type === "event" && m.event === "terminated") {
        const ms = now() - t0;
        const got = { stdout: out, outcome: m.body.outcome, exitCode: m.body.exitCode };
        const want = { stdout: prog.stdout, outcome: prog.outcome, exitCode: prog.exitCode };
        const why = JSON.stringify(got) === JSON.stringify(want) ? null : `${JSON.stringify(got)}, expected ${JSON.stringify(want)}`;
        eng.send({ command: "disconnect" });
        return why ? { ok: false, ms, why } : { ok: true, ms };
      }
    }
  } catch (e) {
    return { ok: false, ms: now() - t0, why: e.message };
  } finally {
    await eng.close();
  }
}

// From a new session to the entry stop: {initializedMs, entryMs} (`configurationDone`
// to `stopped`), on `prog`.
export async function timeEntry(client, prog, opts = {}) {
  const t0 = now();
  const eng = new SessionTransport(client, { name: prog.name, source: prog.source }, undefined, opts);
  try {
    eng.send({ command: "initialize" });
    let initializedMs = null;
    for (;;) {
      const m = await eng.next();
      if (m === null) throw new Error(`the engine exited${eng.trap ? ` (${eng.trap})` : ""}`);
      if (m.type === "event" && m.event === "initialized") {
        initializedMs = now() - t0;
        break;
      }
    }
    eng.send({ command: "launch", arguments: { program: eng.programPath(), stopOnEntry: true } });
    const t1 = now();
    eng.send({ command: "configurationDone" });
    for (;;) {
      const m = await eng.next();
      if (m === null) throw new Error(`the engine exited${eng.trap ? ` (${eng.trap})` : ""}`);
      if (m.type === "event" && m.event === "stopped") {
        const entryMs = now() - t1;
        eng.send({ command: "disconnect" });
        return { initializedMs, entryMs };
      }
    }
  } finally {
    await eng.close();
  }
}

// The whole suite: every transcript, the entry timing, then every program.
// `log(line)` reports progress; `opts` are the sessions' options. The result:
// {passed, failed, failures, timings, programs, deepest}; `timings.compileMs` is
// the caller's.
// The suite on `client`: the transcripts, then the programs.
export async function runSuite(client, bundle, log = () => {}, opts = {}) {
  const r = { passed: 0, failed: 0, failures: [], timings: {}, programs: [], deepest: null };
  const record = (name, why) => {
    if (why === null) r.passed++;
    else {
      r.failed++;
      r.failures.push({ name, why });
    }
    log(why === null ? `ok ${name}` : `FAIL ${name}: ${why}`);
  };
  for (const t of bundle.transcripts) {
    const t0 = now();
    let why;
    try {
      why = await runTranscript(new SessionTransport(client, t.program, undefined, opts), t.dbg);
    } catch (e) {
      why = `error: ${e.message}`;
    }
    r.timings[`transcript ${t.name}`] = Math.round(now() - t0);
    record(t.name, why);
  }
  const first = bundle.programs[0];
  const e1 = await timeEntry(client, first, opts);
  const e2 = await timeEntry(client, first, opts);
  r.timings.initializedMs = [e1.initializedMs, e2.initializedMs].map(Math.round);
  r.timings.entryMs = [e1.entryMs, e2.entryMs].map(Math.round);
  for (const p of bundle.programs) {
    const res = await runProgram(client, p, opts);
    r.programs.push({ name: p.name, depth: p.depth ?? null, ms: Math.round(res.ms), nativeMs: p.nativeMs, ok: res.ok, trap: res.trap ?? null });
    if (res.ok && p.depth != null && (r.deepest === null || p.depth > r.deepest)) r.deepest = p.depth;
    record(p.name, res.ok ? null : `${res.why}${res.trap ? ` (${res.trap})` : ""}`);
  }
  r.timings.programsMs = r.programs.reduce((s, p) => s + p.ms, 0);
  return r;
}
