// The examples and the build selector through the page (index.html?test&gallery[&build=ID]): the selector
// lists the builds of builds.json with the page's selected and its arguments in every launch; the URL of
// another build keeps the example; then every example of examples.json that lists the page's build is
// picked from the menu (which sets its breakpoints and starts it; `&only=ID,...`: only those), paused where its check says (each
// `continue` by its button) and run to the end its check says, as gallery_test.mjs does in node. Progress
// is POSTed to /log and the result ({passed, failed, failures}) to /result, as selftest.mjs does.

import { pageURL } from "./builds.mjs";
import { $ } from "./dom.mjs";
import { printedLines } from "./examples.mjs";
import { endMismatches, menuGroups, pauseMismatches } from "./gallery.mjs";
import { post, waitFor } from "./selftest.mjs";

const RUN_MS = 300000;
const over = () => ["terminated", "ended"].includes(document.body.dataset.state);
const pausedAfter = (model, gen) => document.body.dataset.state === "paused" && model.snap && model.snap.gen > gen && model.snap.totalFrames !== null;

async function walk(model, build, label, e, check) {
  if (model.session) model.stop();
  const want = e.builds[build.id];
  const sel = $("examples");
  const value = `${label}/${e.id}`;
  sel.value = value;
  if (sel.value !== value) throw new Error("not among the examples");
  let gen = model.gen;
  sel.dispatchEvent(new Event("change"));
  check(`${e.id}: the page's example`, new URLSearchParams(location.search).get("example") === e.id, location.search);
  const bad = [];
  for (const [i, p] of want.pauses.entries()) {
    if (i > 0) $("btn-continue").click();
    await waitFor(`${e.id} pause ${i + 1}`, () => pausedAfter(model, gen) || over(), RUN_MS);
    if (over()) {
      bad.push(`ended (${model.ending?.outcome ?? model.state}) before pause ${i + 1}`);
      break;
    }
    gen = model.snap.gen;
    bad.push(...pauseMismatches(p, model.snap.stopped, model.snap.frames.map((f) => f.name)).map((w) => `pause ${i + 1}: ${w}`));
  }
  if (!over()) {
    await model.setBreakpoints([]);
    await model.setLineBreakpoints([]);
    await model.setFilters([]);
    while (!over()) {
      if (document.body.dataset.state === "paused") {
        gen = model.snap.gen;
        $("btn-continue").click();
      }
      await waitFor(`${e.id}'s end`, () => pausedAfter(model, gen) || over(), RUN_MS);
    }
  }
  bad.push(...endMismatches(want, model.ending, printedLines(model)));
  if (bad.length) bad.push(`the console's last lines: ${JSON.stringify(model.output.slice(-3).map((o) => o.text))}`);
  check(`${e.id} [${build.id}]`, !bad.length, bad.join("; "));
  model.stop();
}

export async function run(model, _bundle, _spec, { gallery, builds, build }) {
  const r = { passed: 0, failed: 0, failures: [] };
  const check = (name, ok, why) => {
    if (ok) r.passed++;
    else {
      r.failed++;
      r.failures.push({ name, why });
    }
    post("log", `${ok ? "ok" : "FAIL"} ${name}${ok ? "" : `: ${why}`}`);
  };
  const only = new URLSearchParams(location.search).get("only")?.split(",") ?? null;
  const sel = $("build");
  check("the selector lists the builds", JSON.stringify([...sel.options].map((o) => o.value)) === JSON.stringify(builds.map((b) => b.id)), [...sel.options].map((o) => o.value));
  check("the selector shows the page's build", sel.value === build.id, sel.value);
  check("the build's arguments go to every launch", JSON.stringify(model.config.buildArgs) === JSON.stringify(build.args), model.config.buildArgs);
  for (const b of builds) {
    const u = new URL(pageURL(new URL("?example=demo/get&test", location.href).href, { build: b.id }, builds));
    check(`the URL of ${b.id} keeps the example`, u.searchParams.get("example") === "demo/get" && (u.searchParams.get("build") ?? builds[0].id) === b.id, u.href);
  }
  if (!gallery) check("examples.json", false, "not served");
  for (const [label, list] of Object.entries(menuGroups(gallery))) {
    for (const e of list.filter((x) => x.builds[build.id] && (!only || only.includes(x.id)))) {
      try {
        await walk(model, build, label, e, check);
      } catch (err) {
        check(`${e.id} [${build.id}]`, false, `${err.name}: ${err.message}`);
        if (model.session) model.stop();
      }
    }
  }
  r.userAgent = navigator.userAgent;
  r.transport = model.client.transport;
  r.build = build.id;
  $("status").textContent = `gallery test [${build.id}]: ${r.passed} passed, ${r.failed} failed`;
  await post("result", JSON.stringify(r));
}
