// The source pane: the session's program by line, the current JS position (the
// selected JS frame's, else the innermost frame with `line > 0`: its line highlighted,
// its node's [lo, hi) underlined), a span the model selects (`selectSpan`), an edit mode (a textarea), an
// open-file input and the examples (the bundle's programs, the demo's and the spec issues'),
// each {name, source, args?, label?, title?, setup?, unrunnable?, key?, demo?} (`key`, else `name`, names it
// in its group). A new program starts a
// session on it. The gutter marks the breakable lines (the engine's breakpointLocations) and the
// line breakpoints, each on the line it resolved to; a click there toggles one. A tab per
// source: the program's (a bundle's entry module), and one for each other module of a
// bundle and each eval or Function source the model has opened, read-only (no edit, no
// breakpoints); the model's `sourceShown` is the one shown.

import { el } from "./dom.mjs";
import { sourceRef } from "./model.mjs";

// Lines split by ECMAScript's LineTerminators (CR LF is one), as Dbg.lineCol does:
// `lines` [{start, end}] in UTF-16 offsets (the terminator excluded), and `cp`, each
// code point's UTF-16 offset (one more at the end).
export function lineTable(text) {
  const lines = [];
  const cp = [];
  let start = 0;
  for (let i = 0; i < text.length; ) {
    cp.push(i);
    const c = text.codePointAt(i);
    const w = c > 0xffff ? 2 : 1;
    if (c === 0x0d && text.charCodeAt(i + 1) === 0x0a) {
      cp.push(i + 1);
      lines.push({ start, end: i });
      i += 2;
      start = i;
    } else if (c === 0x0a || c === 0x0d || c === 0x2028 || c === 0x2029) {
      lines.push({ start, end: i });
      i += w;
      start = i;
    } else i += w;
  }
  cp.push(text.length);
  lines.push({ start, end: text.length });
  return { lines, cp };
}

// A code-point offset as a UTF-16 one.
export function utf16(table, i) {
  return table.cp[Math.min(i, table.cp.length - 1)];
}

// A program name serve.py accepts: a plain file name.
export function programName(name) {
  const n = name.replace(/[^A-Za-z0-9._-]/g, "_").replace(/^[^A-Za-z0-9_]/, "_").slice(0, 128);
  return n || "program.js";
}


const NONE = { line: 0, lo: 0, hi: 0, slo: 0, shi: 0 };

export class SourcePane {
  constructor(model, examples) {
    this.model = model;
    this.examples = examples;
    this.view = document.getElementById("source");
    this.tabs = document.getElementById("source-tabs");
    this.editor = document.getElementById("editor");
    this.name = document.getElementById("program-name");
    this.text = null;
    this.table = null;
    this.rows = [];
    this.marked = NONE;
    this.fillExamples();
    document.getElementById("examples").onchange = (e) => this.pick(e.target.value);
    document.getElementById("open-file").onchange = (e) => this.open(e.target.files[0]);
    document.getElementById("edit").onclick = () => this.edit(true);
    document.getElementById("cancel").onclick = () => this.edit(false);
    document.getElementById("apply").onclick = () => this.apply();
    model.on("change", (what) => {
      if (["program", "sources", "state"].includes(what)) this.renderTabs();
      if (["program", "pause", "frames", "jsFrames", "select", "state", "span", "sources"].includes(what)) this.render();
      if (["program", "breakpoints", "locations", "state", "sources"].includes(what)) this.paintGutter();
    });
    this.view.onclick = (e) => {
      const g = e.target.closest(".gutter");
      if (g && !this.shown()?.ref) this.model.toggleLine(+g.parentElement.dataset.line);
    };
    this.tabs.onclick = (e) => {
      const b = e.target.closest("button");
      if (b) this.model.showSource(+b.dataset.ref);
    };
    this.renderTabs();
    this.render();
  }

  fillExamples() {
    const sel = document.getElementById("examples");
    sel.append(el("option", "", "examples…"));
    for (const [label, list] of Object.entries(this.examples)) {
      const g = el("optgroup");
      g.label = label;
      for (const p of list) {
        const o = el("option", "", p.unrunnable ? `${p.label ?? p.name} (cannot run: ${p.unrunnable})` : (p.label ?? p.name));
        o.value = `${label}/${p.key ?? p.name}`;
        if (p.title) o.title = p.title;
        if (p.demo) o.dataset.demo = p.demo;
        g.append(o);
      }
      sel.append(g);
    }
  }

  pick(value) {
    const label = Object.keys(this.examples).find((l) => value.startsWith(`${l}/`));
    const key = label === undefined ? null : value.slice(label.length + 1);
    const p = label === undefined ? null : this.examples[label].find((x) => (x.key ?? x.name) === key);
    document.getElementById("examples").selectedIndex = 0;
    if (p) this.loadExample(p);
  }

  // An example: started after its setup, or, one the engine cannot run, shown with the reason.
  // `onExample(p)`, if set, is told of it (`notify` false: not).
  loadExample(p, notify = true) {
    const program = p.args?.length ? { name: p.name, source: p.source, args: p.args } : { name: p.name, source: p.source };
    if (notify) this.onExample?.(p);
    if (!p.unrunnable) return this.load(program, p.setup);
    this.edit(false);
    this.model.stop();
    this.model.setProgram(program);
    this.model.log("stderr", `${p.label ?? p.name}: cannot run here: ${p.unrunnable}`);
  }

  async open(file) {
    if (!file) return;
    this.onExample?.({});
    this.load({ name: programName(file.name), source: await file.text() });
    document.getElementById("open-file").value = "";
  }

  // `setup()`, if any, configures the session (an example's breakpoints) before its start.
  load(program, setup) {
    this.edit(false);
    this.model.setProgram(program);
    setup?.();
    this.model.start();
  }

  edit(on) {
    const p = this.model.config.program;
    if (on) this.editor.value = p?.source ?? "";
    this.editor.hidden = !on;
    this.view.hidden = on;
    document.getElementById("edit").hidden = on;
    document.getElementById("apply").hidden = !on;
    document.getElementById("cancel").hidden = !on;
    if (on) this.editor.focus();
  }

  apply() {
    this.onExample?.({});
    const { name = "program.js", args } = this.model.config.program ?? {};
    this.load(args ? { name, source: this.editor.value, args } : { name, source: this.editor.value });
  }

  // The source shown: {name, source, ref}, the program (the session's, else the
  // configuration's) at ref 0, or an open source of the run's (its text "" while it loads).
  shown() {
    const m = this.model;
    const src = m.sourceShown ? m.sources.get(m.sourceShown) : null;
    if (src) return { name: src.name, source: src.text ?? "", ref: src.ref };
    const p = m.program ?? m.config.program;
    return p && { ...p, ref: 0 };
  }

  // The tabs: the program's, then the open sources', the shown one marked; none while
  // there is only the program.
  renderTabs() {
    const m = this.model;
    this.tabs.textContent = "";
    this.tabs.hidden = m.sources.size === 0;
    const p = m.program ?? m.config.program;
    for (const x of [{ ref: 0, name: p?.name ?? "program" }, ...m.sources.values()]) {
      const { ref, name } = x;
      const b = el("button", ref === m.sourceShown ? "on" : "", name);
      b.dataset.ref = ref;
      b.title = !ref ? "the program" : x.module ? `a module of the bundle (sourceReference ${ref}), read-only`
        : `code the run parsed (sourceReference ${ref}), read-only`;
      this.tabs.append(b);
    }
  }

  render() {
    const p = this.shown();
    this.name.textContent = p ? p.name : "no program";
    document.getElementById("edit").hidden = !!p?.ref || !this.editor.hidden;
    if ((p?.source ?? null) !== this.text) this.build(p?.source ?? null);
    let at = this.model.state === "paused" ? this.model.jsPosition() : null;
    if (at && (at.ref ?? 0) !== (p?.ref ?? 0)) at = null;
    let mark = NONE;
    if (this.table) {
      const span = this.model.span;
      mark = {
        line: at ? at.line : 0,
        lo: at ? utf16(this.table, at.lo) : 0,
        hi: at ? utf16(this.table, at.hi) : 0,
        slo: span && !p.ref ? utf16(this.table, span.lo) : 0,
        shi: span && !p.ref ? utf16(this.table, span.hi) : 0,
      };
    }
    const old = this.marked;
    if (Object.keys(mark).every((k) => old[k] === mark[k])) return;
    this.marked = mark;
    const covers = (m, start, end) => (m.hi > start && m.lo <= end && m.hi > m.lo) || (m.shi > start && m.slo <= end && m.shi > m.slo);
    for (const m of [old, mark]) {
      for (let n = 1; n <= this.rows.length; n++) {
        const { start, end } = this.table.lines[n - 1];
        if (n === m.line || covers(m, start, end)) this.paint(n);
      }
    }
    if (mark.shi > mark.slo && (mark.slo !== old.slo || mark.shi !== old.shi)) this.view.querySelector(".selected")?.scrollIntoView({ block: "nearest" });
    else if (mark.line) this.rows[mark.line - 1]?.scrollIntoView({ block: "nearest" });
  }

  build(text) {
    this.text = text;
    this.view.textContent = "";
    this.rows = [];
    this.marked = NONE;
    if (text === null) return;
    this.table = lineTable(text);
    for (let n = 1; n <= this.table.lines.length; n++) {
      const row = el("div", "line");
      row.dataset.line = n;
      row.append(el("span", "gutter", String(n)), el("span", "code"));
      this.rows.push(row);
      this.view.append(row);
      this.paint(n);
    }
    this.paintGutter();
  }

  // The gutter's marks: breakable lines, and each line breakpoint's (verified, pending or
  // not verified).
  paintGutter() {
    if (!this.rows.length) return;
    const m = this.model;
    const shown = this.shown();
    const shows = !shown?.ref && m.program?.name === shown?.name;
    const live = m.session !== null && shows;
    const at = new Map();
    (shown?.ref ? [] : m.lineBreakpoints()).forEach((_, i) => {
      const st = live ? m.lineStatus[i] : null;
      const mark = !st || st.message === "pending" ? "pending" : st.verified ? "verified" : "unverified";
      const n = live ? m.lineOf(i) : m.lineBreakpoints()[i].line;
      if (!at.has(n) || mark === "verified") at.set(n, mark);
    });
    this.rows.forEach((row, i) => {
      const g = row.firstChild;
      const mark = at.get(i + 1);
      g.classList.toggle("breakable", live && !!m.locations?.has(i + 1));
      for (const c of ["bp", "verified", "pending", "unverified"]) g.classList.toggle(c, c === "bp" ? !!mark : c === mark);
    });
  }

  // Line n's text, with the marked node's part underlined and the selected span's marked.
  paint(n) {
    const row = this.rows[n - 1];
    const { start, end } = this.table.lines[n - 1];
    const m = this.marked;
    row.classList.toggle("current", n === m.line);
    const code = row.lastChild;
    code.textContent = "";
    const cuts = new Set([start, end]);
    const parts = [];
    for (const [lo, hi, cls] of [[m.lo, m.hi, "node"], [m.slo, m.shi, "selected"]]) {
      const a = Math.max(lo, start);
      const b = Math.min(hi, end);
      if (hi > lo && a < b) {
        parts.push([a, b, cls]);
        cuts.add(a).add(b);
      }
    }
    const at = [...cuts].sort((x, y) => x - y);
    for (let i = 0; i + 1 < at.length; i++) {
      const cls = parts.filter(([a, b]) => a <= at[i] && at[i + 1] <= b).map((p) => p[2]).join(" ");
      const t = this.text.slice(at[i], at[i + 1]);
      code.append(cls ? el("span", cls, t) : t);
    }
    if (!code.textContent) code.textContent = " ";
  }
}
