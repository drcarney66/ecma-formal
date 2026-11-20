// The heap pane: `specHeap` pages of the heap by address, of every kind or one (record,
// list, object, env), each row the cell's address, kind, type and summary. The cells new
// since the last pause and the changed ones (`stopped.spec.diff`) are marked, and the
// changed ones have a view of their own. A row expands to its cell's tree; a cell that
// existed at the last pause shows its parts then and now side by side (`specDiff`), the
// changed ones named. A jump field, and any tree's cell link, show one cell. The diff's
// summary links to the new cells, the changed ones and the execution contexts.

import { $, el } from "./dom.mjs";
import { Tree } from "./tree.mjs";

// The addresses a page covers: of every kind, and of one (Dbg.heapLimit).
export const HEAP_PAGE = 100;
export const KIND_PAGE = 1000;

// A List cell's length from its type ("List (n)"), else 0.
export function listLength(type) {
  const m = /^List \((\d+)\)$/.exec(type ?? "");
  return m ? Number(m[1]) : 0;
}

// An address typed in the jump field ("12" or "#12"), or null.
export function parseAddr(text) {
  const m = /^\s*#?(\d+)\s*$/.exec(text);
  return m ? Number(m[1]) : null;
}

// specDiff's two sides as rows {name, old, now, changed}: the parts now, then the ones
// gone; `old` null where the part (or the cell) did not exist.
export function diffRows(d) {
  const old = new Map((d.old?.variables ?? []).map((v) => [v.name, v.value]));
  const now = d.new?.variables ?? [];
  const changed = new Set(d.changed);
  const rows = now.map((v) => ({ name: v.name, old: old.has(v.name) ? old.get(v.name) : null, now: v.value, changed: changed.has(v.name) }));
  for (const [name, value] of old) {
    if (!now.some((v) => v.name === name)) rows.push({ name, old: value, now: null, changed: changed.has(name) });
  }
  return rows;
}

// The parts of `stopped.spec.diff`'s summary, each {text, view}: the new cells, the
// changed ones (`+` if truncated) and, if so, the stack changed; [] at the first pause.
export function diffParts(diff) {
  if (!diff) return [];
  const [lo, hi] = diff.newCells;
  const n = diff.changed?.length ?? 0;
  const parts = [
    { text: `${hi - lo} new cell${hi - lo === 1 ? "" : "s"}`, view: { mode: "new" }, title: `[${lo}, ${hi})` },
    { text: `${n}${diff.truncated ? "+" : ""} changed`, view: { mode: "changed" }, title: diff.truncated ? "truncated: more cells changed" : "" },
  ];
  if (diff.stackChanged) parts.push({ text: "stack changed", view: { state: true }, title: "the execution context stack" });
  return parts;
}

// The summary in one line.
export function diffLine(diff) {
  const parts = diffParts(diff);
  return parts.length ? `since the last pause: ${parts.map((p) => p.text).join(", ")}` : "first pause: no diff";
}

// The summary as links: the cells into the heap pane, the stack into the state pane.
export function diffSummary(model, diff) {
  const parts = diffParts(diff);
  const box = el("span", "diff-summary");
  if (!parts.length) {
    box.textContent = diffLine(diff);
    return box;
  }
  box.append("since the last pause: ");
  parts.forEach((p, i) => {
    const a = el("a", "diff-link", p.text);
    a.dataset.view = p.view.mode ?? "state";
    if (p.title) a.title = p.title;
    a.onclick = () => (p.view.state ? model.openState() : model.openHeap(p.view));
    box.append(...(i ? [", ", a] : [a]));
  });
  return box;
}

export class HeapPane {
  constructor(model) {
    this.model = model;
    this.list = $("heap");
    this.range = $("heap-range");
    this.kind = $("heap-kind");
    this.addr = $("heap-addr");
    this.summary = $("heap-diff");
    this.tree = new Tree(model);
    // {mode: "range", from} or {mode: "changed"}; the kind filter is the select's.
    this.view = { mode: "range", from: 0 };
    this.focus = null;
    this.olds = new Set();
    this.size = 0;
    this.token = 0;
    this.visible = false;
    this.stale = true;
    this.kind.onchange = () => this.render();
    $("heap-prev").onclick = () => this.page(-1);
    $("heap-next").onclick = () => this.page(1);
    $("heap-new").onclick = () => model.openHeap({ mode: "new" });
    $("heap-changed").onclick = () => model.openHeap({ mode: "changed" });
    const go = () => {
      const a = parseAddr(this.addr.value);
      this.addr.classList.toggle("bad", a === null);
      if (a !== null) model.openHeap({ addr: a });
    };
    $("heap-go").onclick = go;
    this.addr.onkeydown = (e) => e.key === "Enter" && go();
    model.on("change", (what) => {
      if (what === "heap") this.ask(model.heapAsk);
      else if (what === "pause" || what === "state") {
        this.summary.textContent = "";
        if (model.state === "paused") this.summary.append(diffSummary(model, model.diff()));
        this.render();
      }
    });
  }

  show(on) {
    this.visible = on;
    if (on && this.stale) this.render();
  }

  // The addresses a page covers with the current filter.
  count() {
    return this.kind.value ? KIND_PAGE : HEAP_PAGE;
  }

  page(dir) {
    if (this.view.mode !== "range") return;
    const from = this.view.from + dir * this.count();
    if (from < 0 || from >= this.size) return;
    this.view = { mode: "range", from };
    this.render();
  }

  // A view the model asked for: a cell (expanded and marked), the new cells, the changed.
  ask(v) {
    const diff = this.model.diff();
    this.focus = null;
    this.kind.value = "";
    if (v.addr !== undefined) {
      this.view = { mode: "range", from: v.addr };
      this.focus = v.addr;
      this.tree.expanded.add(`#${v.addr}`);
    } else if (v.mode === "new") this.view = { mode: "range", from: diff ? diff.newCells[0] : 0 };
    else this.view = { mode: "changed" };
    this.render();
  }

  async render() {
    const m = this.model;
    if (!this.visible) {
      this.stale = true;
      return;
    }
    this.stale = false;
    const token = ++this.token;
    if (m.state !== "paused") {
      this.list.textContent = "";
      this.range.textContent = "";
      return;
    }
    const diff = m.diff();
    const kind = this.kind.value || undefined;
    let cells = [];
    if (this.view.mode === "changed") {
      const got = await Promise.all((diff?.changed ?? []).map((a) => m.heap(a, 1)));
      if (token !== this.token) return;
      cells = got.flatMap((b) => b?.cells ?? []).filter((c) => !kind || c.kind === kind);
      if (got[0]) this.size = got[0].heapSize;
      const n = diff?.changed?.length ?? 0;
      this.range.textContent = `changed since the last pause: ${n}${diff?.truncated ? "+ (truncated)" : ""}`;
    } else {
      const { from } = this.view;
      const body = await m.heap(from, this.count(), kind);
      if (token !== this.token) return;
      cells = body?.cells ?? [];
      this.size = body?.heapSize ?? 0;
      const to = Math.min(from + this.count(), this.size);
      this.range.textContent = `[${from}, ${to}) of ${this.size}`;
    }
    $("heap-prev").disabled = this.view.mode !== "range" || this.view.from === 0;
    $("heap-next").disabled = this.view.mode !== "range" || this.view.from + this.count() >= this.size;
    $("heap-changed").disabled = !diff?.changed?.length;
    $("heap-new").disabled = !diff || diff.newCells[0] === diff.newCells[1];
    this.list.textContent = "";
    for (const c of cells) this.list.append(this.row(c, diff));
    if (!cells.length) this.list.append(el("li", "empty", "no cells"));
    const f = this.focus === null ? null : this.list.querySelector(`li.cell[data-addr="${this.focus}"]`);
    if (f) {
      f.classList.add("focus");
      f.scrollIntoView({ block: "nearest" });
    }
  }

  // A cell's row: its tree below it, and its old/new view.
  row(c, diff) {
    const li = el("li", "cell");
    li.dataset.addr = c.addr;
    const [lo, hi] = diff?.newCells ?? [0, 0];
    if (diff && c.addr >= lo && c.addr < hi) li.classList.add("new");
    if (diff?.changed?.includes(c.addr)) li.classList.add("changed");
    const row = el("div", "row");
    row.append(el("span", "toggle", "▸"), el("span", "addr", `#${c.addr}`), el("span", "kind", c.kind), el("span", "type", c.type), el("span", "summary", c.summary));
    li.append(row);
    this.tree.expandable(li, row, `#${c.addr}`, { variablesReference: c.variablesReference, indexedVariables: listLength(c.type) });
    if (diff && c.addr < lo) {
      const box = el("div", "olds");
      const btn = el("button", "old-new", "old/new");
      btn.title = "this cell at the last pause and now";
      const open = (on) => {
        box.hidden = !on;
        btn.classList.toggle("on", on);
        if (on) this.olds.add(c.addr);
        else this.olds.delete(c.addr);
        if (on && !box.firstChild) this.oldNew(box, c.addr);
      };
      btn.onclick = (e) => {
        e.stopPropagation();
        open(box.hidden);
      };
      row.append(btn);
      li.append(box);
      open(this.olds.has(c.addr));
    }
    return li;
  }

  // Cell `addr` at the last pause and now, part by part.
  async oldNew(box, addr) {
    box.append(el("div", "loading", "…"));
    const d = await this.model.spec("specDiff", { addr });
    box.textContent = "";
    if (!d) return box.append(el("div", "empty", "no diff"));
    box.append(el("div", "names", d.changed.length ? `changed: ${d.changed.join(", ")}` : "no part changed"));
    const t = el("table", "parts");
    const head = el("tr");
    head.append(el("th", "", ""), el("th", "", "last pause"), el("th", "", "now"));
    t.append(head);
    for (const r of diffRows(d)) {
      const tr = el("tr", r.changed ? "changed" : "");
      tr.dataset.name = r.name;
      tr.append(el("td", "name", r.name), el("td", "old", r.old ?? "—"), el("td", "now", r.now ?? "—"));
      t.append(tr);
    }
    box.append(t);
  }
}
