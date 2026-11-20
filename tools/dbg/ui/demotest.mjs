// The demo's scripts through the page (index.html?test&demo): each program of
// tools/dbg/demo/script.mjs picked from the examples (which sets its breakpoints and
// starts it), each stop reached by its control's button and what the panes show there
// checked as demo_test.mjs checks the model: the status bar, the step pane and its
// listing, the source's line and node, the spec and JS stacks, the inspector's Slots and
// a slot's cell expanded, then shown in the heap pane by its link. Progress is POSTed to
// /log and the result ({passed, failed, failures}) to /result, as selftest.mjs does.

import { DEMOS, mismatches } from "../demo/script.mjs";
import { $ } from "./dom.mjs";
import { post, waitFor } from "./selftest.mjs";

const all = (sel, root = document) => [...root.querySelectorAll(sel)];
const text = (sel) => document.querySelector(sel)?.textContent ?? "";
const tab = (name) => document.querySelector(`#tabs button[data-tab="${name}"]`).click();
const slotRow = (name) => document.querySelector(`#inspect [data-path="Slots/${name}"]`);
const kidsOf = (li) => all(":scope > .kids > li.var", li);
const valueOf = (li) => li.querySelector(":scope > .row .value")?.textContent;

// The session's end: the program's, or the engine's (an exit or a trap).
const over = () => ["terminated", "ended"].includes(document.body.dataset.state);

const BUTTONS = { continue: "btn-continue", next: "btn-next", in: "btn-in", out: "btn-out", jsNext: "btn-jsnext", jsIn: "btn-jsin", jsOut: "btn-jsout" };

// A pause after generation `gen`, its panes rendered: frames, JS stack, Slots and listing.
function shown(model, gen) {
  const snap = model.snap;
  if (document.body.dataset.state !== "paused" || !snap || snap.gen <= gen) return false;
  if (snap.totalFrames === null || !snap.jsFrames || !snap.scopes.get(0)) return false;
  const slots = snap.scopes.get(0).find((x) => x.name === "Slots");
  const loaded = slots ? model.loaded(slots.variablesReference) : [];
  if (!loaded) return false;
  const s = snap.stopped.spec;
  return (
    all("#stack .frame").length === snap.frames.length &&
    all("#jsstack .frame").length === snap.jsFrames.length &&
    model.listing(s.secId, s.idx ?? 0) !== undefined &&
    !document.querySelector("#step .listing-note") &&
    (!slots || kidsOf(document.querySelector('#inspect [data-path="Slots"]')).length === loaded.length)
  );
}

// What the page shows, as script.mjs's stops name it; `cells`: the slots whose cells are expanded.
async function observe(cells) {
  const st = /paused \(([^):)]*)[^]*?\) at (\S+) (\S+) · depth /.exec($("status").textContent) ?? [];
  const path = st[3] ?? null;
  const steptext = text("#step .steptext");
  const line = document.querySelector("#source .line.current")?.dataset.line;
  const o = {
    reason: st[1] ?? null,
    alg: st[2] ?? null,
    path,
    text: steptext.startsWith(`${path}. `) ? steptext.slice(path.length + 2) : steptext,
    current: document.querySelector("#step li.lstep.current")?.dataset.path ?? null,
    line: line ? +line : null,
    node: line ? all("#source .node").map((e) => e.textContent).join("\n") : null,
    frames: all("#stack .frame").map((li) => `${li.querySelector(".name").textContent} ${li.querySelector(".path").textContent}`),
    js: all("#jsstack .frame .name").map((e) => e.textContent),
    slots: Object.fromEntries(kidsOf(document.querySelector('#inspect [data-path="Slots"]')).map((li) => [li.querySelector(".name").textContent, valueOf(li)])),
    cell: {},
    heap: {},
  };
  for (const name of cells) {
    const li = slotRow(name);
    const link = li?.querySelector(":scope > .row a.cell");
    if (!link) continue;
    if (li.querySelector(":scope > .kids")?.hidden !== false) li.querySelector(".row").click();
    await waitFor(`${name}'s parts`, () => kidsOf(li).length > 0);
    o.cell[name] = Object.fromEntries(kidsOf(li).map((k) => [k.querySelector(".name").textContent, valueOf(k)]));
    const addr = link.dataset.addr;
    link.click();
    await waitFor(`${name}'s cell in the heap`, () => !$("heap-pane").hidden && document.querySelector(`#heap li.cell.focus[data-addr="${addr}"] [data-path^="#${addr}/"]`));
    o.heap[name] = addr;
    tab("inspect");
  }
  return o;
}

async function walk(model, demo, check) {
  if (model.session) model.stop();
  const sel = $("examples");
  const before = model.gen;
  // The demo's group, or on the site the tour's example of the program.
  const opt = [...sel.options].find((o) => o.value === `tools/dbg/demo/${demo.program}`) ?? [...sel.options].find((o) => o.dataset.demo === demo.program);
  if (!opt) throw new Error(`${demo.program} is not among the examples`);
  sel.value = opt.value;
  sel.dispatchEvent(new Event("change"));
  let gen = before;
  for (const [i, stop] of demo.stops.entries()) {
    const what = `${demo.program} stop ${i + 1} (${stop.do})`;
    if (i > 0) {
      const b = $(BUTTONS[stop.do]);
      if (b.disabled) throw new Error(`${what}: its button is disabled in state ${model.state}`);
      b.click();
    }
    await waitFor(what, () => shown(model, gen) || over());
    if (over()) throw new Error(`${what}: ended before the stop (${$("status").textContent}; console: ${text("#console").slice(-300)})`);
    gen = model.snap.gen;
    const o = await observe(Object.keys(stop.cell ?? {}));
    const bad = mismatches(stop, o);
    for (const name of Object.keys(stop.cell ?? {})) if (!o.heap[name]) bad.push(`${name}: no cell link`);
    check(`${what} at ${stop.alg ?? o.alg} ${stop.path ?? o.path}`, !bad.length, bad.join("; "));
  }
  $(BUTTONS.continue).click();
  await waitFor(`${demo.program}'s end`, () => document.body.dataset.state === "terminated");
  check(`${demo.program}: the end`, text("#console").includes(`terminated: ${demo.end} (exit code`), text("#console"));
  model.stop();
}

export async function run(model) {
  const r = { passed: 0, failed: 0, failures: [] };
  const check = (name, ok, why) => {
    if (ok) r.passed++;
    else {
      r.failed++;
      r.failures.push({ name, why });
    }
    post("log", `${ok ? "ok" : "FAIL"} ${name}${ok ? "" : `: ${why}`}`);
  };
  for (const demo of DEMOS) {
    try {
      await walk(model, demo, check);
    } catch (e) {
      check(demo.program, false, `${e.name}: ${e.message}`);
      if (model.session) model.stop();
    }
  }
  r.userAgent = navigator.userAgent;
  r.transport = model.client.transport;
  $("status").textContent = `demo test: ${r.passed} passed, ${r.failed} failed`;
  await post("result", JSON.stringify(r));
}
