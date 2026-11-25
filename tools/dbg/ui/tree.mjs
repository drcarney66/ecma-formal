// Lazy trees of `variables`, for the inspector, heap and state panes: a row per
// variable, its children loaded when it is first expanded, the parts that differ from
// the previous pause marked (presentationHint "changed"), Lists paged by LIST_PAGE, and
// a link that opens a value's heap cell in the heap pane. What was expanded stays
// expanded at the next pause, by its path of names.

import { el } from "./dom.mjs";
import { LIST_PAGE, cellOf } from "./model.mjs";

export class Tree {
  constructor(model, expanded = new Set()) {
    this.model = model;
    this.expanded = expanded;
  }

  // A variable's row and its children.
  node(path, v, scope = false) {
    const li = el("li", scope ? "scope" : "var");
    li.dataset.path = path;
    const row = el("div", "row");
    row.append(el("span", "toggle", v.variablesReference ? "▸" : " "), el("span", "name", v.name));
    if (!scope) {
      row.append(": ", el("span", "value", typeof v.value === "string" ? v.value : JSON.stringify(v.value)));
      if (v.type) row.append(" ", el("span", "type", v.type));
      const addr = cellOf(v);
      if (addr !== null) row.append(" ", this.cellLink(addr));
    }
    if (v.presentationHint?.attributes?.includes("changed")) li.classList.add("changed");
    li.append(row);
    this.expandable(li, row, path, v);
    return li;
  }

  // A link that shows cell `addr` in the heap pane.
  cellLink(addr) {
    const a = el("a", "cell", `#${addr}`);
    a.dataset.addr = addr;
    a.title = `cell #${addr} in the heap`;
    a.onclick = (e) => {
      e.stopPropagation();
      this.model.openHeap({ addr });
    };
    return a;
  }

  // `row` (in `li`) toggles the children of `v`, loaded when first expanded.
  expandable(li, row, path, v) {
    if (!v.variablesReference) return;
    const toggle = row.querySelector(".toggle");
    const kids = el("ul", "kids");
    kids.hidden = true;
    li.append(kids);
    let loaded = false;
    const open = (on) => {
      kids.hidden = !on;
      toggle.textContent = on ? "▾" : "▸";
      li.classList.toggle("open", on);
      if (on) this.expanded.add(path);
      else this.expanded.delete(path);
      if (on && !loaded) {
        loaded = true;
        this.load(kids, path, v, 0);
      }
    };
    row.onclick = () => open(kids.hidden);
    if (this.expanded.has(path)) open(true);
  }

  // The children of `v` from `start`: all of them, or a List's page by page.
  async load(kids, path, v, start) {
    const paged = (v.indexedVariables ?? 0) > LIST_PAGE;
    const wait = el("li", "loading", "…");
    kids.append(wait);
    const vs = paged
      ? await this.model.variables(v.variablesReference, start, LIST_PAGE)
      : await this.model.variables(v.variablesReference);
    wait.remove();
    if (!vs) return;
    for (const c of vs) kids.append(this.node(`${path}/${c.name}`, c));
    const next = start + LIST_PAGE;
    if (paged && next < v.indexedVariables) {
      const more = el("li", "more", `more (${next} of ${v.indexedVariables})`);
      more.onclick = () => {
        more.remove();
        this.load(kids, path, v, next);
      };
      kids.append(more);
    }
  }
}
