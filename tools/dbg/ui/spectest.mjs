// The spec issues' examples through the page (index.html?test&examples): each runnable one of
// spec-examples.json picked from the examples, stopped on entry; `continue` to the report's
// step where it has a breakpoint (the first stop there), then on to the end: a pause at the
// model's stop where the `stop` filter is on, and the outcome, exit code and printed lines of the
// model's run (`expect`, examples.mjs). With `&example=ID`, the page has opened ID first, which
// is checked too. Progress is POSTed to /log and the result ({passed, failed, failures}) to
// /result, as selftest.mjs does.

import { $ } from "./dom.mjs";
import { endMismatches, printedLines, stopMismatches } from "./examples.mjs";
import { post, waitFor } from "./selftest.mjs";

const GROUP = "docs/spec-issues";
const RUN_MS = 600000;
const MAX_STOPS = 3;

const over = () => ["terminated", "ended"].includes(document.body.dataset.state);
const pausedAfter = (model, gen) => document.body.dataset.state === "paused" && model.snap && model.snap.gen > gen;

async function walk(model, e, check) {
  if (model.session) model.stop();
  const sel = $("examples");
  const gen0 = model.gen;
  sel.value = `${GROUP}/${e.name}`;
  if (sel.value !== `${GROUP}/${e.name}`) throw new Error("not among the examples");
  sel.dispatchEvent(new Event("change"));
  await waitFor(`${e.id}'s entry`, () => pausedAfter(model, gen0) || over(), RUN_MS);
  if (over()) throw new Error(`ended before its entry: ${$("status").textContent}`);
  check(`${e.id}: stopped on entry`, model.snap.stopped.reason === "entry", $("status").textContent);
  let gen = model.snap.gen;
  $("btn-continue").click();
  if (e.breakpoints.length) {
    const bp = e.breakpoints[0];
    await waitFor(`${e.id}'s breakpoint`, () => pausedAfter(model, gen) || over(), RUN_MS);
    const s = model.snap?.stopped;
    const at = s && `${s.reason} at ${s.spec.secId} ${s.spec.path}`;
    check(`${e.id}: continue lands on ${bp.alg} ${bp.path}`, s?.reason === "breakpoint" && s.spec.secId === bp.alg && s.spec.path === bp.path, at ?? $("status").textContent);
    if (!over()) {
      await model.setBreakpoints([]);
      gen = model.snap.gen;
      $("btn-continue").click();
    }
  }
  const stops = [];
  for (;;) {
    await waitFor(`${e.id}'s end`, () => over() || pausedAfter(model, gen), RUN_MS);
    if (over()) break;
    stops.push(model.snap.stopped);
    if (stops.length > MAX_STOPS) break;
    gen = model.snap.gen;
    $("btn-continue").click();
  }
  const pauses = stopMismatches(e, stops);
  check(`${e.id}: ${e.filters.includes("stop") ? "a pause at the model's stop" : "no other pause"}`, !pauses.length, pauses.join("; "));
  if (!over()) throw new Error(`still paused: ${$("status").textContent}`);
  const bad = endMismatches(e.expect, model.ending, printedLines(model));
  check(`${e.id}: the end`, !bad.length, bad.join("; "));
}

export async function run(model, _bundle, examples) {
  const r = { passed: 0, failed: 0, failures: [], skipped: [] };
  const check = (name, ok, why) => {
    if (ok) r.passed++;
    else {
      r.failed++;
      r.failures.push({ name, why });
    }
    post("log", `${ok ? "ok" : "FAIL"} ${name}${ok ? "" : `: ${why}`}`);
  };
  const asked = new URLSearchParams(location.search).get("example");
  if (asked) check(`?example=${asked} opened it`, model.config.program?.name === `${asked}.js`, model.config.program?.name);
  check("spec-examples.json lists examples", examples.length > 0, "none");
  for (const e of examples) {
    if (e.unrunnable) {
      r.skipped.push(`${e.id}: ${e.unrunnable}`);
      post("log", `skip ${e.id}: ${e.unrunnable}`);
      continue;
    }
    if (!e.expect) {
      check(e.id, false, "no model run to compare with");
      continue;
    }
    const t0 = performance.now();
    try {
      await walk(model, e, check);
    } catch (err) {
      check(e.id, false, `${err.name}: ${err.message}`);
    }
    if (model.session) model.stop();
    post("log", `${e.id}: ${((performance.now() - t0) / 1000).toFixed(1)} s`);
  }
  r.userAgent = navigator.userAgent;
  r.transport = model.client.transport;
  $("status").textContent = `spec examples test: ${r.passed} passed, ${r.failed} failed`;
  await post("result", JSON.stringify(r));
}
