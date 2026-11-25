// The debugger UI (tools/dbg/ui/index.html, and the site's debugger page): the engine, the model, the
// panes, the controls and their keys, the build selector and the status bar. The engine is the native
// one behind serve.py --engine (client.mjs's native-http transport), or, with `?engine=worker` or the
// page's `data-engine="worker"`, a WebAssembly build of ecma-dbg in a Worker: the build `?build=` names
// in builds.json (builds.mjs), the table's first by default, whose arguments come before a program's own
// in every launch. Its configuration is saved per build. `?example=ID` opens an example (examples.json's,
// the demo's `demo/NAME`, the bundle's `dbg/NAME` and `run/NAME`, or a spec issue's), `?args=` adds
// arguments to it. Where the browser lacks what the WebAssembly build needs (support.mjs), the page says
// so and shows the example's source instead. The directory of the debugger's files is the page's
// `data-root`, else `../`. `?test` runs selftest.mjs on a configuration kept in memory, `?test&demo`
// demotest.mjs, `?test&examples` spectest.mjs, `?test&gallery` gallerytest.mjs.

import { DbgClient } from "../client.mjs";
import { BreakpointsPane, MemoryStorage, loadConfig } from "./breakpoints.mjs";
import { FALLBACK, chooseBuild, exampleBuild, pageURL, parseArgs, readBuilds, storageKey } from "./builds.mjs";
import { ConsolePane } from "./console.mjs";
import { $, el } from "./dom.mjs";
import { findExample, menuGroups, programOf } from "./gallery.mjs";
import { HeapPane } from "./heap.mjs";
import { InspectPane } from "./inspect.mjs";
import { JsStackPane } from "./jsstack.mjs";
import { Model } from "./model.mjs";
import { SourcePane } from "./source.mjs";
import { StatePane } from "./state.mjs";
import { StackPane } from "./stack.mjs";
import { StepPane } from "./step.mjs";
import { BROWSERS, missing } from "./support.mjs";

const params = new URLSearchParams(location.search);
if (window.parent !== window) document.documentElement.classList.add("in-iframe");
const test = params.has("test");
const worker = (params.get("engine") ?? document.body.dataset.engine ?? "").startsWith("worker");
const root = new URL(document.body.dataset.root ?? "../", location.href);
const version = document.body.dataset.version ?? "";

const ISOLATION_WAIT_MS = 10000;
const SPEC_GROUP = "docs/spec-issues";
const SAMPLE = { name: "program.js", source: 'function f(a) {\n  return a + 1;\n}\nprint(f(1));\n' };

function assetURL(name) {
  const u = new URL(name, root);
  if (version) u.searchParams.set("v", version);
  return u;
}

// A JSON file of the debugger's directory, or null.
async function json(name) {
  try {
    const r = await fetch(assetURL(name), { cache: "no-cache" });
    return r.ok ? await r.json() : null;
  } catch {
    return null;
  }
}

// A Worker build needs SharedArrayBuffer: on a page its server does not isolate,
// coi-serviceworker.js (index.html) reloads it under its service worker, so wait for that.
async function isolation() {
  if (globalThis.crossOriginIsolated) return;
  if (navigator.serviceWorker && isSecureContext) await new Promise((r) => setTimeout(r, ISOLATION_WAIT_MS));
  throw new Error("the page is not cross-origin isolated (COOP and COEP, or coi-serviceworker.js)");
}

function makeClient(build, onLoadState) {
  if (worker) {
    const c = DbgClient.lazy(assetURL(build.wasm), { expectedBytes: build.wasmBytes ?? 0 });
    c.onLoadState = onLoadState ?? null;
    return c;
  }
  return DbgClient.connect(root);
}

function mb(bytes) {
  return (bytes / (1024 * 1024)).toFixed(1);
}

async function client(build, onLoadState) {
  if (worker) await isolation();
  return makeClient(build, onLoadState);
}

// The test bundle (dbg-tests.json, scripts/dbg_browser_bundle.py), if served, and its programs as examples.
// The built site (`data-engine` set on `<body>`) ships `examples.json` instead and has no test bundle outside `?test`.
async function bundle() {
  if (document.body.dataset.engine && !test) return { bundle: null, examples: {} };
  try {
    const r = await fetch(new URL("dbg-tests.json", root));
    if (!r.ok) return { bundle: null, examples: {} };
    const b = await r.json();
    const seen = new Set();
    const dbg = [];
    for (const t of b.transcripts) {
      if (t.program && !seen.has(t.program.name)) {
        seen.add(t.program.name);
        dbg.push(t.program);
      }
    }
    const run = b.programs.map(({ name, source }) => ({ name, source }));
    return { bundle: b, examples: { "tests/dbg": dbg, "tests/run": run } };
  } catch {
    return { bundle: null, examples: {} };
  }
}

// The demo's programs (tools/dbg/demo, if served) as examples: picking one sets its
// script's breakpoints, line breakpoints and filters first, and clears stop on entry.
async function demos(model) {
  const scripts = await import(new URL("demo/script.mjs", root).href).then((m) => m.DEMOS, () => []);
  const got = await Promise.all(
    scripts.map(async (d) => {
      const r = await fetch(new URL(`demo/${d.program}`, root)).catch(() => null);
      if (!r?.ok) return null;
      const setup = () => {
        model.setBreakpoints(d.breakpoints ?? []);
        model.setLineBreakpoints((d.lines ?? []).map((line) => ({ line })));
        model.setFilters(d.filters ?? []);
        if ($("stop-on-entry").checked) $("stop-on-entry").click();
      };
      return { name: d.program, source: await r.text(), setup };
    }),
  );
  return got.filter(Boolean);
}

// The spec issues' examples (spec-examples.json, scripts/dbg_spec_examples.py, if served): picking
// one sets its breakpoints and filters, clears the line breakpoints and sets stop on entry, so
// that `continue` goes to the report's step.
async function specExamples(model) {
  const r = await fetch(assetURL("spec-examples.json"), { cache: "no-cache" }).catch(() => null);
  if (!r?.ok) return [];
  const { examples } = await r.json();
  const setup = (e) => () => {
    model.setBreakpoints(e.breakpoints);
    model.setLineBreakpoints([]);
    model.setFilters(e.filters);
    if (!$("stop-on-entry").checked) $("stop-on-entry").click();
  };
  return examples.map((e) => ({ ...e, setup: setup(e) }));
}

// What each control does, and when it is enabled.
function controls(model) {
  const paused = () => model.state === "paused";
  return {
    start: { run: () => model.start(), on: () => model.config.program !== null },
    continue: { run: () => (model.state === "running" ? model.pause() : model.cont()), on: () => paused() || model.state === "running" },
    pause: { run: () => model.pause(), on: () => model.state === "running" },
    jsnext: { run: () => model.jsNext(), on: paused },
    jsin: { run: () => model.jsIn(), on: paused },
    jsout: { run: () => model.jsOut(), on: paused },
    next: { run: () => model.next(), on: paused },
    in: { run: () => model.stepIn(), on: paused },
    out: { run: () => model.stepOut(), on: paused },
    instruction: { run: () => model.stepInstruction(), on: paused },
    stop: { run: () => model.stop(), on: () => model.session !== null },
  };
}

// Single-key shortcuts (when focus is outside inputs) alongside F8–F11:
// c / F8 continue or pause; s / Alt+F10 spec next; i / Alt+F11 spec in; o / Alt+Shift+F11 spec out;
// n / F10 JS statement next; r restart; F11 / Shift+F11 JS in/out; F9 one transition.
function key(e, inField = false) {
  if (e.key === "F8") return "continue";
  if (e.key === "F9") return "instruction";
  const spec = e.altKey ? "" : "js";
  if (e.key === "F10") return `${spec}next`;
  if (e.key === "F11") return `${spec}${e.shiftKey ? "out" : "in"}`;
  if (inField || e.metaKey || e.ctrlKey || e.altKey) return null;
  switch (e.key) {
    case "c": return "continue";
    case "s": return "next";
    case "i": return "in";
    case "o": return "out";
    case "n": return "jsnext";
    case "r": return "start";
    default: return null;
  }
}

// The right column's tabs: Inspector, Heap and State; a pane in `panes` is told when it
// is shown. A cell or view asked of the heap pane shows its tab, as `openState` the state's.
function tabs(model, panes) {
  const buttons = [...document.querySelectorAll("#tabs button")];
  const show = (name) => {
    for (const b of buttons) {
      const on = b.dataset.tab === name;
      b.classList.toggle("on", on);
      $(`${b.dataset.tab}-pane`).hidden = !on;
      panes[b.dataset.tab]?.show(on);
    }
  };
  for (const b of buttons) b.onclick = () => show(b.dataset.tab);
  model.on("change", (what) => {
    if (what === "heap") show("heap");
    else if (what === "openState") show("state");
  });
  globalThis.dbg.tab = show;
}

// A span {line, column, endLine, endColumn} as `l:c–l:c`.
const spanText = (s) => `${s.line}:${s.column}–${s.endLine}:${s.endColumn}`;

export function statusLine(model) {
  const st = model.snap?.stopped;
  switch (model.state) {
    case "paused": {
      const s = st.spec;
      const why = [st.reason, st.description, s.filter, s.stop].filter(Boolean).join(": ");
      const stmt = st.js?.statement ? ` · statement ${spanText(st.js.statement)}` : "";
      return `paused (${why}) at ${s.alg} ${s.path} · depth ${s.depth}${stmt} · steps ${s.steps} · transitions ${s.transitions}`;
    }
    case "terminated":
      return `terminated: ${model.ending.outcome} (exit code ${model.ending.exitCode})`;
    case "running":
      return "running";
    case "setup":
      return "starting";
    case "ended":
      return "no session";
    default:
      return "no session: start one (▶)";
  }
}

// The selector: one entry per build, the page's selected; picking another swaps the build and lazy client in place.
function selector(builds, build, onSelect) {
  const sel = $("build");
  for (const b of builds) {
    const o = el("option", "", b.label);
    o.value = b.id;
    o.title = b.description;
    sel.append(o);
  }
  sel.value = build.id;
  sel.disabled = builds.length < 2;
  $("build-note").textContent = build.description;
  sel.onchange = () => {
    const next = chooseBuild(builds, sel.value);
    if (onSelect) onSelect(next);
    else location.href = pageURL(location.href, { build: sel.value }, builds);
  };
}

// The example `id` asks for: examples.json's, a demo's, the bundle's or a spec issue's; null if none.
function lookup(id, gallery, groups, spec) {
  const g = findExample(gallery, id);
  if (g) return g;
  const s = spec.find((x) => x.id === id);
  if (s) return s;
  const [kind, name] = id.split("/");
  const group = { demo: "tools/dbg/demo", dbg: "tests/dbg", run: "tests/run" }[kind];
  return groups[group]?.find((p) => p.name === `${name}.js`) ?? null;
}

// The page without its engine: why, and the asked-for example's source.
function unsupported(why, example) {
  $("panes").hidden = true;
  $("controls").hidden = true;
  $("unsupported").hidden = false;
  $("unsupported-why").textContent = why;
  $("unsupported-what").textContent =
    `The debugger runs the specification's machine as WebAssembly with 64-bit memory, which ${BROWSERS} have. Safari has no 64-bit WebAssembly memory yet.`;
  const ex = $("unsupported-examples");
  ex.textContent = "Every example's source, and what it shows, is on the ";
  const a = el("a", "", "examples page");
  a.href = new URL("../examples.html", root).href;
  ex.append(a, ".");
  if (example?.source) {
    $("unsupported-source").hidden = false;
    $("unsupported-source").textContent = example.source;
  }
  $("status").textContent = "no engine";
}

async function main() {
  const status = $("status");
  const builds = await json("builds.json").then((j) => (j ? readBuilds(j) : FALLBACK)).catch(() => FALLBACK);
  let build = chooseBuild(builds, params.get("build"));
  const [b, gallery] = await Promise.all([bundle(), json("examples.json")]);
  const asked = params.get("example");
  if (worker) {
    const lacks = missing();
    if (lacks.length) {
      selector(builds, build);
      unsupported(`This browser lacks ${lacks.join(", ")}.`, asked && findExample(gallery, asked));
      if (test) throw new Error(`the browser lacks ${lacks.join(", ")}`);
      return;
    }
  }
  status.textContent = worker ? "preparing debugger" : "connecting";
  const storage = test ? new MemoryStorage() : localStorage;
  let store = storageKey(build.id);
  let update = () => {};
  const c = await client(build, () => update());
  const saved = loadConfig(storage, store);
  const model = new Model(c, {
    program: saved.program ?? b.examples["tests/dbg"]?.find((p) => p.name === "stepping.js") ?? SAMPLE,
    breakpoints: Array.isArray(saved.breakpoints) ? saved.breakpoints : [],
    lineBreakpoints: saved.lineBreakpoints && typeof saved.lineBreakpoints === "object" ? saved.lineBreakpoints : {},
    filters: Array.isArray(saved.filters) ? saved.filters : [],
    stopOnEntry: saved.stopOnEntry === true,
    buildArgs: build.args,
  });
  globalThis.dbg = { model, build };
  const setBuild = (next) => {
    if (!next || next.id === build.id) return false;
    if (model.session) model.stop();
    build = next;
    store = storageKey(build.id);
    globalThis.dbg.build = build;
    $("build").value = build.id;
    $("build-note").textContent = build.description;
    model.listings.clear();
    model.config.buildArgs = build.args;
    model.client = makeClient(build, () => update());
    return true;
  };
  selector(builds, build, (next) => {
    const hadSession = model.session !== null || model.state === "terminated";
    if (!setBuild(next)) return;
    history.replaceState(null, "", pageURL(location.href, { build: build.id }, builds));
    update();
    if (!test && hadSession && model.config.program) model.start();
  });
  // An example's setup: its breakpoints, line breakpoints, filters, and expanded inspector paths, stop on entry cleared.
  let inspect = null;
  const setupOf = (e) => () => {
    model.setBreakpoints(e.breakpoints ?? []);
    model.setLineBreakpoints((e.lines ?? []).map((line) => ({ line })));
    model.setFilters(e.filters ?? []);
    if (inspect) {
      inspect.tree.expanded = new Set(["Slots", ...(Array.isArray(e.expand) ? e.expand : [])]);
    }
    if ($("stop-on-entry").checked) $("stop-on-entry").click();
  };
  const tour = gallery ? menuGroups(gallery) : {};
  for (const list of Object.values(tour)) for (const e of list) e.setup = setupOf(e);
  const [demo, spec] = await Promise.all([gallery ? [] : demos(model), specExamples(model)]);
  const groups = { ...tour, ...(demo.length ? { "tools/dbg/demo": demo } : {}), ...(spec.length ? { [SPEC_GROUP]: spec } : {}), ...b.examples };
  const source = new SourcePane(model, groups);
  new JsStackPane(model);
  new StackPane(model);
  new StepPane(model);
  inspect = new InspectPane(model);
  tabs(model, { heap: new HeapPane(model), state: new StatePane(model) });
  new ConsolePane(model);
  new BreakpointsPane(model, storage, store);
  // An example picked is the page's `?example=` (so that a reload, or another build, opens it again);
  // outside test mode, picking a proposal example (or an example unsupported by the active build) switches
  // synchronously to that example's primary build before `SourcePane.loadExample` starts the session.
  source.onExample = (p) => {
    const id = p.id ?? null;
    if (!test && id) setBuild(exampleBuild(p, build, builds));
    history.replaceState(null, "", pageURL(location.href, { example: id, args: null, build: build.id }, builds));
    update();
  };

  const ctl = controls(model);
  for (const [name, c] of Object.entries(ctl)) $(`btn-${name}`).onclick = () => c.on() && c.run();
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && window.parent !== window) {
      window.parent.postMessage({ type: "deck-escape" }, location.origin);
      return;
    }
    const tag = e.target?.tagName;
    const inField = tag === "INPUT" || tag === "TEXTAREA" || tag === "SELECT" || !!e.target?.isContentEditable;
    if (!inField && !e.metaKey && !e.ctrlKey && !e.altKey) {
      const tabMap = { "1": "inspect", "2": "heap", "3": "state" };
      if (tabMap[e.key] && globalThis.dbg?.tab) {
        e.preventDefault();
        globalThis.dbg.tab(tabMap[e.key]);
        return;
      }
    }
    const k = key(e, inField);
    if (!k) return;
    e.preventDefault();
    if (ctl[k].on()) ctl[k].run();
  });
  const entry = $("stop-on-entry");
  entry.checked = model.config.stopOnEntry;
  entry.onchange = () => {
    model.config.stopOnEntry = entry.checked;
    model.emit("config");
  };
  const progBox = $("wasm-progress");
  const progLabel = $("wasm-progress-label");
  const progPct = $("wasm-progress-pct");
  const progFill = $("wasm-progress-fill");
  update = () => {
    for (const [name, c] of Object.entries(ctl)) $(`btn-${name}`).disabled = !c.on();
    $("btn-start").textContent = model.session ? "↻ restart (r)" : "▶ start (r)";
    $("btn-continue").textContent = model.state === "running" ? "⏸ pause (c)" : "▶ continue (c)";
    document.body.dataset.state = model.state;
    const isLoading = worker && !!model.client?.loading;
    const p = model.client?.progress;
    if (progBox) {
      progBox.hidden = !isLoading;
      if (isLoading) {
        if (p?.phase === "compiling") {
          progLabel.textContent = `Compiling ${build.wasm}…`;
          progPct.textContent = p.loaded > 0 ? `${mb(p.loaded)} MB` : "";
          progBox.classList.add("indeterminate");
          progFill.style.width = "";
        } else if (p && p.total > 0) {
          const pct = Math.min(100, Math.round((p.loaded / p.total) * 100));
          progLabel.textContent = `Downloading ${build.wasm} · ${mb(p.loaded)} / ${mb(p.total)} MB`;
          progPct.textContent = `${pct}%`;
          progBox.classList.remove("indeterminate");
          progFill.style.width = `${pct}%`;
        } else {
          progLabel.textContent = `Downloading ${build.wasm}` + (p?.loaded > 0 ? ` · ${mb(p.loaded)} MB` : "…");
          progPct.textContent = "";
          progBox.classList.add("indeterminate");
          progFill.style.width = "";
        }
      }
    }
    const loading = isLoading ? `loading ${build.wasm} · ` : "";
    status.textContent = `${worker ? build.label : "native"} · ${loading}${statusLine(model)}`;
  };
  model.on("change", update);
  update();
  if (asked) {
    const e = lookup(asked, gallery, groups, spec);
    const more = parseArgs(params.get("args"));
    if (e) {
      const setup = e.setup ?? (e.breakpoints ? setupOf(e) : undefined);
      source.loadExample({ ...e, ...(more ? { args: [...(e.args ?? []), ...more] } : {}), setup }, false);
    } else model.log("stderr", `no example ${asked}`);
  }
  if (test) {
    const page = params.has("demo") ? "./demotest.mjs" : params.has("examples") ? "./spectest.mjs" : params.has("gallery") ? "./gallerytest.mjs" : "./selftest.mjs";
    (await import(page)).run(model, b.bundle, spec, { gallery, builds, build });
  }
}

main().catch((e) => {
  $("status").textContent = `${e.name}: ${e.message}`;
  if (test) {
    const r = { passed: 0, failed: 1, failures: [{ name: "page", why: `${e.name}: ${e.message}` }] };
    fetch(new URL("result", location.origin), { method: "POST", body: JSON.stringify(r) }).catch(() => {});
  }
});
