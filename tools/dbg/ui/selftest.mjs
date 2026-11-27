// The UI's self-test (index.html?test): a scripted session that drives the DOM, on
// tests/dbg/stepping.js from the bundle. A breakpoint at sec-evaluatecall 3 through
// the form, the example picked (which starts the session); the panes at the stop, the
// algorithm's listing with step 3 current; a breakpoint at step 5 by its gutter;
// stepIn and stepOut by their buttons; a slot expanded; the JS stack pane; continue to
// step 5, its breakpoint removed by the gutter, continue to the end and the console. Then heap.js and tdz.js with the debugger filter: the heap pane (a new object
// cell by kind, expanded; the heap paged; `o.a` changed with old 1 and new 2; a jump to
// an address; a tree's cell link), the state pane (the running context first, the
// program's root selected in the source, the host group collapsed) and a TDZ binding
// before and after its initialization. Then linebp.js, stopped on entry: line breakpoints by
// gutter clicks (pending, then verified, the blank line's moved), hit; statement stepping by
// F10, F11 and Shift+F11 with the statement in the status bar, a spec step by Alt+F10, and
// a breakpoint toggled off. Then eval.js: F11 into the eval code opens its tab (`eval #1`,
// read-only, its text and the position shown), the program's tab and the JS stack's
// (script) show the program, its (eval) row the eval code again. Then bundle.js, a d8 bundle:
// its module files as tabs (the entry module the program's), a module's text read-only, a
// line breakpoint in the entry hit, F11 into a module. Progress is POSTed to /log and the result
// ({passed, failed, failures}) to /result, as test.mjs does (serve.py --test).

import { $ } from "./dom.mjs";

const root = new URL("../", location.href);
let posted = Promise.resolve();
// POSTs one after another, in order.
export const post = (path, body) => (posted = posted.then(() => fetch(new URL(path, root), { method: "POST", body }).catch(() => {})));
const text = (sel) => document.querySelector(sel)?.textContent ?? "";

// Resolves once `pred()` holds, polled; rejects after `ms` with `what`.
export function waitFor(what, pred, ms = 60000) {
  return new Promise((res, rej) => {
    const t0 = performance.now();
    const poll = () => {
      let ok = false;
      try {
        ok = pred();
      } catch {}
      if (ok) res();
      else if (performance.now() - t0 > ms) rej(new Error(`timed out waiting for ${what} (status: ${$("status").textContent})`));
      else setTimeout(poll, 50);
    };
    poll();
  });
}

const click = (id) => $(id).click();
const all = (sel) => [...document.querySelectorAll(sel)];
const tab = (name) => document.querySelector(`#tabs button[data-tab="${name}"]`).click();
const heapRows = () => all("#heap li.cell");
const rowOf = (sel) => document.querySelector(`[data-path="${sel}"]`);
const valueOf = (li) => li?.querySelector(":scope > .row .value")?.textContent;

function pick(name) {
  const sel = $("examples");
  sel.value = `tests/dbg/${name}`;
  sel.dispatchEvent(new Event("change"));
}

async function cont(what) {
  click("btn-continue");
  await waitFor(what, () => paused() && document.querySelector("#diff .diff-link"));
}

// heap.js: the heap and state panes.
async function heapPanes(check, model) {
  for (const b of all("#breakpoints .remove")) b.click();
  const box = document.querySelector('#filters input[data-filter="debugger"]');
  if (!box.checked) box.click();
  pick("heap.js");
  await waitFor("heap.js's first pause", () => paused() && text("#diff").includes("first pause"));
  check("heap: first pause", text("#diff") === "first pause: no diff", text("#diff"));
  await cont("heap.js's second pause");
  check("heap: summary", /^since the last pause: \d+ new cells, \d+ changed$/.test(text("#diff")), text("#diff"));
  document.querySelector('#diff a[data-view="new"]').click();
  await waitFor("the new cells", () => !$("heap-pane").hidden && document.querySelector("#heap li.cell.new"));
  check("heap: the tab", document.querySelector("#tabs button.on")?.dataset.tab === "heap" && $("inspect-pane").hidden, text("#tabs button.on"));
  const kind = $("heap-kind");
  kind.value = "object";
  kind.dispatchEvent(new Event("change"));
  await waitFor("the new objects", () => heapRows().length && heapRows().every((li) => li.querySelector(".kind").textContent === "object"));
  const o = heapRows().find((li) => li.querySelector(".summary").textContent.endsWith("{a}"));
  check("heap: a new object cell", o?.classList.contains("new") && o.querySelector(".type").textContent === "Object", heapRows().map((li) => li.textContent));
  const addr = o.dataset.addr;
  o.querySelector(".row").click();
  await waitFor("the object's parts", () => rowOf(`#${addr}/a`));
  check("heap: o.a is 1", valueOf(rowOf(`#${addr}/a`)) === "1", rowOf(`#${addr}/a`).textContent);
  const extRow = rowOf(`#${addr}/[[Extensible]]`)?.querySelector(":scope > .row")?.textContent ?? "";
  check("heap: expanded slot spacing", /\[\[Extensible\]\]: true Boolean$/.test(extRow), extRow);

  kind.value = "list";
  kind.dispatchEvent(new Event("change"));
  $("heap-addr").value = "0";
  click("heap-go");
  await waitFor("the heap from 0", () => text("#heap-range").startsWith("[0, 100) of"));
  check("heap: the jump clears the kind", kind.value === "" && heapRows().length === 100, kind.value);
  kind.value = "list";
  kind.dispatchEvent(new Event("change"));
  await waitFor("Lists from 0", () => text("#heap-range").startsWith("[0, 1000) of") && heapRows().every((li) => li.querySelector(".kind").textContent === "list"));
  // The next pages until one has Lists.
  let from = 0;
  do {
    from += 1000;
    click("heap-next");
    await waitFor(`Lists from ${from}`, () => text("#heap-range").startsWith(`[${from}, ${from + 1000}) of`) && (heapRows().length || document.querySelector("#heap .empty")));
  } while (!heapRows().length && !$("heap-next").disabled);
  const inPage = (li) => li.querySelector(".kind").textContent === "list" && +li.dataset.addr >= from && +li.dataset.addr < from + 1000;
  check("heap: a later page of Lists", heapRows().length > 0 && heapRows().every(inPage), text("#heap-range"));
  for (; from > 0; from -= 1000) click("heap-prev");
  await waitFor("the first page again", () => text("#heap-range").startsWith("[0, 1000) of"));
  check("heap: prev", $("heap-prev").disabled, "");

  await cont("heap.js's third pause");
  check("heap: summary links", text("#heap-diff").includes(" changed") && document.querySelector('#heap-diff a[data-view="changed"]'), text("#heap-diff"));
  document.querySelector('#heap-diff a[data-view="changed"]').click();
  await waitFor("the changed cells", () => text("#heap-range").startsWith("changed since the last pause") && document.querySelector("#heap li.cell.changed .old-new"));
  const ch = document.querySelector("#heap li.cell.changed");
  ch.querySelector(".old-new").click();
  await waitFor("its old and new parts", () => ch.querySelector('tr[data-name="[[Value]]"]'));
  const tr = ch.querySelector('tr[data-name="[[Value]]"]');
  check("heap: [[Value]] 1 → 2", tr.classList.contains("changed") && tr.querySelector(".old").textContent === "1" && tr.querySelector(".now").textContent === "2", tr.textContent);
  check("heap: its changed parts named", ch.querySelector(".olds .names").textContent === "changed: [[Value]]", ch.querySelector(".olds").textContent);

  $("heap-addr").value = `#${addr}`;
  $("heap-addr").dispatchEvent(new KeyboardEvent("keydown", { key: "Enter" }));
  await waitFor("o by its address", () => document.querySelector(`#heap li.cell.focus[data-addr="${addr}"]`) && rowOf(`#${addr}/a`));
  const a = rowOf(`#${addr}/a`);
  check("heap: o.a now 2, changed", valueOf(a) === "2" && a.classList.contains("changed"), a.textContent);
  const of = document.querySelector(`#heap li.cell[data-addr="${addr}"]`);
  of.querySelector(".old-new").click();
  await waitFor("o's old and new parts", () => of.querySelector('tr[data-name="a"]'));
  const ta = of.querySelector('tr[data-name="a"]');
  check("heap: o's a 1 → 2", ta.classList.contains("changed") && ta.querySelector(".old").textContent === "1" && ta.querySelector(".now").textContent === "2", ta.textContent);

  tab("state");
  await waitFor("the state pane", () => document.querySelector("#state-contexts li") && document.querySelector("#state-roots li"));
  const first = document.querySelector("#state-contexts > li > .row .name").textContent;
  check("state: the running context first", first.endsWith(" running"), first);
  check("state: derived facts", all("#state-derived > li > .row .name").map((e) => e.textContent).includes("active function"), text("#state-derived"));
  check("state: host collapsed", !$("state-host").open && text("#state-host").includes("transitions"), text("#state-host"));
  check("state: SDO nodes", text("#state-sdos").includes("DebuggerStatement"), text("#state-sdos"));
  document.querySelector("#state-roots li.program").click();
  await waitFor("the program selected", () => document.querySelector("#source .selected"));
  const shown = all("#source .line")
    .filter((l) => l.querySelector(".selected"))
    .map((l) => [...l.querySelectorAll(".selected")].map((e) => e.textContent).join(""))
    .join("\n");
  check("state: the root's span in the source", shown === model.program.source.trimEnd(), shown);
  const link = document.querySelector("#state-contexts a.cell");
  const target = link.dataset.addr;
  link.click();
  await waitFor("a cell link", () => !$("heap-pane").hidden && document.querySelector(`#heap li.cell.focus[data-addr="${target}"] [data-path^="#${target}/"]`));
  check("tree: a cell opens in the heap, expanded", text(`#heap li.cell.focus[data-addr="${target}"] .type`) !== "", target);
  click("btn-gc");
  await waitFor("gc summary", () => text("#heap-diff").includes("gc: collected") && $("status").textContent.includes("gc -"));
  check("heap: gc button updates status and diff", text("#heap-diff").includes("live of") && text("#heap-range").includes("live)"), text("#heap-diff"));
  click("btn-continue");
  await waitFor("heap.js's end", () => document.body.dataset.state === "terminated");
  check("heap: the end", text("#console").includes("terminated: normal: 2"), text("#console"));
}

// tdz.js: a let binding before and after its initialization, in the state pane.
async function tdzBinding(check) {
  tab("state");
  pick("tdz.js");
  const path = ["derived/running execution context", "[[LexicalEnvironment]]", "[[DeclarativeRecord]]", "x"];
  await waitFor("tdz.js's first pause", () => paused() && document.querySelector("#state-derived li"));
  for (let i = 1; i < path.length; i++) {
    const at = path.slice(0, i).join("/");
    rowOf(at).querySelector(".row").click();
    await waitFor(`${at}'s parts`, () => rowOf(`${path.slice(0, i + 1).join("/")}`));
  }
  const x = path.join("/");
  check("tdz: x in its TDZ", valueOf(rowOf(x)) === "TDZ" && !rowOf(x).classList.contains("changed"), rowOf(x).textContent);
  await cont("tdz.js's second pause");
  await waitFor("x again", () => rowOf(x) && valueOf(rowOf(x)) !== undefined);
  check("tdz: x initialized, changed", valueOf(rowOf(x)) === "1" && rowOf(x).classList.contains("changed"), rowOf(x).textContent);
  click("btn-continue");
  await waitFor("tdz.js's end", () => document.body.dataset.state === "terminated");
}
// The JS stack pane at stepping.js's call: (script) and the realm's (host); selecting
// each selects its innermost spec frame, marks its range and shows its position.
async function jsStack(check, model) {
  await waitFor("the JS stack", () => model.snap?.jsFrames && all("#jsstack .frame").length === model.snap.jsFrames.length);
  const names = all("#jsstack .frame .name").map((e) => e.textContent);
  check("jsstack: names", JSON.stringify(names) === '["(script)","(host)"]', names);
  check("jsstack: the script's position", text("#jsstack .frame .pos") === "stepping.js:4:1", text("#jsstack .frame"));
  for (const f of [...model.snap.jsFrames].reverse()) {
    const lo = f.spec.frames.lo;
    document.querySelector(`#jsstack .frame[data-id="${f.id}"]`).click();
    await waitFor(`JS frame ${f.id} selected`, () => document.querySelector("#stack .frame.selected")?.dataset.id === `${lo}`);
    const sel = document.querySelector("#jsstack .frame.selected");
    check(`jsstack: ${f.name} selected`, sel?.dataset.id === `${f.id}`, sel?.textContent);
    const range = all("#stack .frame.jsrange").map((e) => +e.dataset.id);
    check(`jsstack: ${f.name}'s range marked`, range.length > 0 && range.every((i) => lo <= i && i < f.spec.frames.hi), range);
    const line = document.querySelector("#source .line.current")?.dataset.line;
    check(`jsstack: ${f.name}'s source line`, f.line > 0 ? line === `${f.line}` : line === undefined, line);
  }
}
// linebp.js: line breakpoints by the gutter, statement stepping by the keys.
async function lineBreakpoints(check) {
  const gutter = (n) => document.querySelector(`#source .line[data-line="${n}"] .gutter`);
  const current = () => document.querySelector("#source .line.current")?.dataset.line;
  const press = (key, opts = {}) => document.dispatchEvent(new KeyboardEvent("keydown", { key, bubbles: true, ...opts }));
  const status = () => $("status").textContent;
  const entry = $("stop-on-entry");
  if (!entry.checked) entry.click();
  pick("linebp.js");
  await waitFor("linebp.js's entry", () => paused() && status().includes("(entry)"));
  gutter(7).click();
  await waitFor("line 7's breakpoint", () => gutter(7).classList.contains("bp") && text("#breakpoints .line-bp").includes("pending"));
  check("linebp: pending at the entry", gutter(7).classList.contains("pending"), gutter(7).className);
  gutter(9).click();
  await waitFor("line 9's breakpoint", () => all("#breakpoints .line-bp").length === 2 && text("#breakpoints").includes("line 9 pending"));
  click("btn-continue");
  await waitFor("line 7's hit", () => paused() && current() === "7");
  check("linebp: the hit's status", status().includes("paused (breakpoint)") && status().includes("statement 7:3–7:13"), status());
  await waitFor("the breakable lines", () => gutter(5).classList.contains("breakable"));
  check("linebp: verified on 7", gutter(7).classList.contains("verified"), gutter(7).className);
  check("linebp: 9 moved to 10", gutter(10).classList.contains("verified") && !gutter(9).classList.contains("bp") && text("#breakpoints").includes("→ 10:1"), text("#breakpoints"));
  check("linebp: 9 not breakable", !gutter(9).classList.contains("breakable") && gutter(2).classList.contains("breakable"), gutter(9).className);
  press("F10");
  await waitFor("F10's stop", () => paused() && current() === "7");
  check("linebp: F10 to the next iteration", status().includes("paused (breakpoint)"), status());
  gutter(7).click();
  await waitFor("line 7's breakpoint removed", () => !gutter(7).classList.contains("bp") && all("#breakpoints .line-bp").length === 1);
  click("btn-continue");
  await waitFor("line 10's hit", () => paused() && current() === "10");
  press("F11");
  await waitFor("F11 into f", () => paused() && current() === "2");
  check("linebp: F11's statement", status().includes("paused (step)") && status().includes("statement 2:3–2:17"), status());
  press("F11", { shiftKey: true });
  await waitFor("Shift+F11 out to the call", () => paused() && current() === "10");
  check("linebp: out at the call", text("#source .node") === "f(s)", text("#source .node"));
  const before = status();
  press("F10", { altKey: true });
  await waitFor("Alt+F10's spec step", () => paused() && status() !== before);
  check("linebp: Alt+F10 a spec step", status().includes("paused (step)") && current() === "10", status());
  for (const b of all("#breakpoints .line-bp .remove")) b.click();
  entry.click();
  click("btn-continue");
  await waitFor("linebp.js's end", () => document.body.dataset.state === "terminated");
  check("linebp: the end", text("#console").includes("terminated: normal"), text("#console"));
}

// eval.js: a tab per source the run parsed.
async function evalSources(check) {
  const gutter = (n) => document.querySelector(`#source .line[data-line="${n}"] .gutter`);
  const current = () => document.querySelector("#source .line.current")?.dataset.line;
  const on = () => text("#source-tabs button.on");
  const shownText = () => all("#source .line .code").map((e) => e.textContent).join("\n");
  const entry = $("stop-on-entry");
  if (!entry.checked) entry.click();
  pick("eval.js");
  await waitFor("eval.js's entry", () => paused() && $("status").textContent.includes("(entry)"));
  check("eval: no tabs with the program alone", $("source-tabs").hidden, $("source-tabs").outerHTML);
  gutter(2).click();
  await waitFor("line 2's breakpoint", () => gutter(2).classList.contains("bp"));
  click("btn-continue");
  await waitFor("line 2's hit", () => paused() && current() === "2");
  document.dispatchEvent(new KeyboardEvent("keydown", { key: "F11", bubbles: true }));
  await waitFor("F11 into the eval code", () => paused() && on() === "eval #1" && current() === "1");
  const tabs = all("#source-tabs button").map((b) => b.textContent);
  check("eval: the tabs", !$("source-tabs").hidden && JSON.stringify(tabs) === '["eval.js","eval #1"]', tabs);
  check("eval: its text", shownText() === "var c = a + 1;\nc * 2", shownText());
  check("eval: the node", text("#source .node") === "var c = a + 1;", text("#source .node"));
  check("eval: read-only", $("edit").hidden && !gutter(1).classList.contains("breakable"), $("edit").hidden);
  document.querySelector('#source-tabs button[data-ref="0"]').click();
  await waitFor("the program's tab", () => on() === "eval.js");
  check("eval: the program, no position in it", shownText().startsWith("var a = 1;") && current() === undefined, current());
  await waitFor("the JS stack", () => all("#jsstack .frame").length === 3);
  check("eval: (eval)'s row", text("#jsstack .frame .name") === "(eval)" && text("#jsstack .frame .pos") === "eval #1:1:1", text("#jsstack .frame"));
  document.querySelector('#jsstack .frame[data-id="1"]').click();
  await waitFor("(script) selected", () => on() === "eval.js" && current() === "2");
  document.querySelector('#jsstack .frame[data-id="0"]').click();
  await waitFor("(eval) selected", () => on() === "eval #1" && current() === "1");
  gutter(1).click();
  check("eval: no breakpoint by its gutter", !gutter(1).classList.contains("bp"), gutter(1).className);
  document.querySelector('#source-tabs button[data-ref="0"]').click();
  await waitFor("the program's tab again", () => on() === "eval.js");
  gutter(2).click();
  await waitFor("line 2's breakpoint removed", () => !gutter(2).classList.contains("bp"));
  entry.click();
  click("btn-continue");
  await waitFor("eval.js's end", () => document.body.dataset.state === "terminated");
  check("eval: the end", text("#console").includes("terminated: normal"), text("#console"));
}

async function bundleSources(check) {
  const gutter = (n) => document.querySelector(`#source .line[data-line="${n}"] .gutter`);
  const current = () => document.querySelector("#source .line.current")?.dataset.line;
  const on = () => text("#source-tabs button.on");
  const shownText = () => all("#source .line .code").map((e) => e.textContent).join("\n");
  const tabs = () => all("#source-tabs button").map((b) => b.textContent);
  const entry = $("stop-on-entry");
  if (!entry.checked) entry.click();
  pick("bundle.js");
  await waitFor("bundle.js's entry and modules", () => paused() && JSON.stringify(tabs()) === '["main.mjs","lib/math.mjs","lib/show.mjs"]' && shownText().startsWith("import { show }"));
  check("bundle: the module files listed", !$("source-tabs").hidden, tabs());
  check("bundle: the entry module's text", shownText().trimEnd() === 'import { show } from "./lib/show.mjs";\nshow(21);', shownText());
  document.querySelector('#source-tabs button[data-ref="1073741824"]').click();
  await waitFor("lib/math.mjs's tab", () => on() === "lib/math.mjs" && shownText().startsWith("export function double"));
  check("bundle: a module read-only", $("edit").hidden, $("edit").hidden);
  document.querySelector('#source-tabs button[data-ref="0"]').click();
  await waitFor("the entry's tab", () => on() === "main.mjs");
  gutter(2).click();
  await waitFor("line 2's breakpoint", () => gutter(2).classList.contains("bp"));
  click("btn-continue");
  await waitFor("line 2's hit", () => paused() && current() === "2");
  document.dispatchEvent(new KeyboardEvent("keydown", { key: "F11", bubbles: true }));
  await waitFor("F11 into lib/show.mjs", () => paused() && on() === "lib/show.mjs" && current() === "3");
  check("bundle: the module's node", text("#source .node") === "print(double(x));", text("#source .node"));
  document.querySelector('#source-tabs button[data-ref="0"]').click();
  await waitFor("the entry's tab again", () => on() === "main.mjs");
  gutter(2).click();
  await waitFor("line 2's breakpoint removed", () => !gutter(2).classList.contains("bp"));
  entry.click();
  click("btn-continue");
  await waitFor("bundle.js's end", () => document.body.dataset.state === "terminated");
  check("bundle: the end", text("#console").includes("terminated: normal: undefined"), text("#console"));
}

const paused = () => document.body.dataset.state === "paused";
const loaded = () => document.querySelector("#stack .frame") && document.querySelector('#inspect [data-path="Slots"] .kids li.var');

export async function run(model, bundle) {
  const r = { passed: 0, failed: 0, failures: [] };
  const check = (name, ok, got) => {
    if (ok) r.passed++;
    else {
      r.failed++;
      r.failures.push({ name, why: `got ${JSON.stringify(got)}` });
    }
    post("log", `${ok ? "ok" : "FAIL"} ${name}`);
  };
  try {
    if (!bundle?.transcripts.some((t) => t.program?.name === "stepping.js")) throw new Error("no stepping.js in the bundle");
    $("bp-alg").value = "sec-evaluatecall";
    $("bp-path").value = "3";
    click("bp-add");
    check("breakpoint listed", text("#breakpoints .bp").includes("sec-evaluatecall 3"), text("#breakpoints"));
    const sel = $("examples");
    sel.value = "tests/dbg/stepping.js";
    sel.dispatchEvent(new Event("change"));

    await waitFor("the breakpoint's stop", () => paused() && loaded());
    check("status", $("status").textContent.includes("paused (breakpoint) at EvaluateCall 3 · depth 5"), $("status").textContent);
    check("breakpoint verified", document.querySelector("#breakpoints .bp.verified") !== null, text("#breakpoints"));
    check("stack top", text("#stack .frame .name") === "EvaluateCall", text("#stack .frame"));
    check("stack run", text("#stack .run").startsWith("run 0"), text("#stack .run"));
    check("stack source line", [...document.querySelectorAll("#stack .pos")].some((e) => e.textContent === "stepping.js:4"), text("#stack"));
    check("step sec-id", text("#step .secid a") === "sec-evaluatecall", text("#step .secid"));
    check("step link", document.querySelector("#step .secid a").href === "https://tc39.es/ecma262/#sec-evaluatecall", "");
    check("step text", text("#step .steptext").startsWith("3. Let argList be ? ArgumentListEvaluation"), text("#step .steptext"));
    check("source line", document.querySelector("#source .line.current")?.dataset.line === "4", text("#source .line.current"));
    check("source node", text("#source .node") === "f(2)", text("#source .node"));
    check("diff line", text("#diff").length > 0, text("#diff"));
    const names = [...document.querySelectorAll('#inspect [data-path="Slots"] > .kids > li.var > .row .name')].map((e) => e.textContent);
    check("slots", names.includes("func") && names.includes("argList"), names);
    await waitFor("the listing", () => document.querySelector("#step li.lstep.current"));
    const paths = all("#step li.lstep").map((li) => li.dataset.path).join();
    check("listing: the steps", paths === "1,1.a,1.a.i,1.b,1.b.i,1.b.ii,1.b.iii,2,2.a,3,4,5,6,7", paths);
    check("listing: step 3 current", document.querySelector("#step li.lstep.current").dataset.path === "3", text("#step li.lstep.current"));
    check("listing: step 3's breakpoint", document.querySelector('#step li.lstep[data-path="3"]').classList.contains("bp"), text("#step ol.listing"));
    document.querySelector('#spec-notation button[data-notation="spectec"]').click();
    check("spectec toggle: step text", text("#step .steptext") === "3. let argList = ? sdo ArgumentListEvaluation(argumentListNode)", text("#step .steptext"));
    check("spectec toggle: signature", text("#step .signature").startsWith('def @sec-evaluatecall "EvaluateCall" (kind ao params [func :'), text("#step .signature"));
    check("spectec toggle: stack text", text("#stack .frame .text") === "let argList = ? sdo ArgumentListEvaluation(argumentListNode)", text("#stack .frame .text"));
    check("spectec toggle: listing step 3", text('#step li.lstep[data-path="3"] .stext').trim() === "let argList = ? sdo ArgumentListEvaluation(argumentListNode)", text('#step li.lstep[data-path="3"] .stext'));
    document.querySelector('#spec-notation button[data-notation="ecma"]').click();
    check("ecma toggle: restored", text("#step .steptext").startsWith("3. Let argList be ? ArgumentListEvaluation"), text("#step .steptext"));
    document.querySelector('#step li.lstep[data-path="5"] .gutter').click();
    await waitFor("step 5's breakpoint", () => document.querySelector('#step li.lstep.bp[data-path="5"]') && document.querySelectorAll("#breakpoints .bp.verified").length === 2);
    check("listing: a gutter's breakpoint listed", text("#breakpoints").includes("sec-evaluatecall#0 5"), text("#breakpoints"));

    click("btn-in");
    await waitFor("stepIn's stop", () => paused() && loaded() && text("#step .alg .name") === "ArgumentListEvaluation");
    check("stepIn status", $("status").textContent.includes("(step) at ArgumentListEvaluation 1 · depth 6"), $("status").textContent);
    check("stepIn source", text("#source .node").length > 0, text("#source .node"));

    click("btn-out");
    await waitFor("stepOut's stop", () => paused() && loaded() && text("#step .secid a") === "sec-evaluatecall");
    check("stepOut depth", $("status").textContent.includes("depth 5"), $("status").textContent);

    const func = document.querySelector('#inspect [data-path="Slots/func"]');
    check("slot row spacing", /\bfunc: #\d+ Object #\d+$/.test(func.querySelector(":scope > .row").textContent), func.querySelector(":scope > .row").textContent);
    func.querySelector(".row").click();
    await waitFor("func's parts", () => func.querySelector(".kids li.var"));
    check("slot expanded", func.querySelectorAll(".kids li.var").length > 0, func.textContent);
    const firstPart = func.querySelector(".kids li.var > .row").textContent;
    check("expanded slot part spacing", /: .+ \S+/.test(firstPart) && !/falseBoolean|trueBoolean/.test(firstPart), firstPart);

    const other = document.querySelectorAll("#stack .frame")[1];
    other.click();
    await waitFor("frame 1 selected", () => document.querySelector("#stack .frame.selected")?.dataset.id === "1" && document.querySelector('#inspect [data-path="Slots"]'));
    check("frame 1's step", text("#step .alg .name") === "Evaluation", text("#step .alg"));
    await jsStack(check, model);

    click("btn-continue");
    await waitFor("step 5's stop", () => paused() && loaded() && document.querySelector("#step li.lstep.current"));
    check("listing: the break at step 5", $("status").textContent.includes("(breakpoint) at EvaluateCall 5"), $("status").textContent);
    check("listing: step 5 current", document.querySelector("#step li.lstep.current").dataset.path === "5", text("#step li.lstep.current"));
    document.querySelector('#step li.lstep[data-path="5"] .gutter').click();
    await waitFor("step 5's breakpoint removed", () => !document.querySelector('#step li.lstep.bp[data-path="5"]'));
    check("listing: the gutter removes it", !text("#breakpoints").includes("#0 5") && all("#breakpoints .bp").length === 1, text("#breakpoints"));
    click("btn-continue");
    await waitFor("the end", () => document.body.dataset.state === "terminated");
    check("console", text("#console").includes("terminated: normal: 2 (exit code 0)"), text("#console"));
    check("status at the end", $("status").textContent.includes("terminated: normal: 2"), $("status").textContent);
    model.stop();
    await heapPanes(check, model);
    await tdzBinding(check);
    model.stop();
    await lineBreakpoints(check);
    model.stop();
    await evalSources(check);
    model.stop();
    await bundleSources(check);
    model.stop();
  } catch (e) {
    r.failed++;
    r.failures.push({ name: "selftest", why: `${e.name}: ${e.message}` });
    post("log", `FAIL selftest: ${e.message}`);
  }
  r.userAgent = navigator.userAgent;
  r.transport = model.client.transport;
  $("status").textContent = `self-test: ${r.passed} passed, ${r.failed} failed`;
  await post("result", JSON.stringify(r));
}
