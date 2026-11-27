// The state pane: the execution context stack (frame 0's "Execution contexts" scope, the
// running context first, then the facts state.md §7 derives from it), and `specState`:
// the Agent Record, the Symbols and parses so far, each parse's root (a click on the
// program's selects its span in the source), the Parse Nodes of the running SDOs, the
// arguments Lists passed, and the host / model group, collapsed.

import { $, el } from "./dom.mjs";
import { Tree } from "./tree.mjs";

const CONTEXT = /^\[\d+\]/;

// The "Execution contexts" scope's variables: the contexts, the running one first, and
// the derived facts.
export function splitContexts(vars) {
  return { contexts: vars.filter((v) => CONTEXT.test(v.name)).reverse(), facts: vars.filter((v) => !CONTEXT.test(v.name)) };
}

// The root of the program's parse: the first parsed from source.
export function programRoot(roots) {
  return roots.filter((r) => r.kind === "source").sort((a, b) => a.parse - b.parse)[0] ?? null;
}

export class StatePane {
  constructor(model) {
    this.model = model;
    this.root = $("state");
    this.tree = new Tree(model);
    this.hostOpen = false;
    this.built = null;
    this.visible = false;
    model.on("change", (what) => {
      if (what === "gc") this.built = null;
      if (["pause", "scopes", "state", "gc"].includes(what)) this.render();
    });
  }

  show(on) {
    this.visible = on;
    if (on) this.render();
  }

  section(title, note) {
    const h = el("h3", "", title);
    if (note) h.append(el("span", "note", ` ${note}`));
    this.root.append(h);
  }

  list(id) {
    const ul = el("ul", "tree");
    ul.id = id;
    this.root.append(ul);
    return ul;
  }

  async render() {
    const m = this.model;
    const snap = m.state === "paused" ? m.snap : null;
    if (!snap) {
      this.root.textContent = "";
      this.built = null;
      return;
    }
    const ctxs = snap.scopes.get(0)?.find((x) => x.name === "Execution contexts");
    if (!this.visible || this.built === snap.gen || !ctxs) return;
    this.built = snap.gen;
    const [vars, st] = await Promise.all([m.variables(ctxs.variablesReference), m.spec("specState")]);
    if (m.snap !== snap) return;
    this.root.textContent = "";
    if (vars) {
      const { contexts, facts } = splitContexts(vars);
      this.section("Execution contexts", `(${contexts.length}, the running one first)`);
      const cs = this.list("state-contexts");
      for (const v of contexts) cs.append(this.tree.node(`contexts/${v.name}`, v));
      this.section("Derived from the stack", "(§7)");
      const fs = this.list("state-derived");
      for (const v of facts) fs.append(this.tree.node(`derived/${v.name}`, v));
    }
    if (!st) return this.root.append(el("div", "empty", "no state"));
    this.section("Agent Record");
    this.list("state-agent").append(this.tree.node("agent", st.agent));
    const heapNote = st.liveCells !== undefined && st.liveCells < st.heapSize ? `${st.liveCells} live / ${st.heapSize} cells` : `${st.heapSize} cells`;
    this.root.append(el("div", "counts", `Symbols ${st.symbols} · parses ${st.parses} · contexts ${st.contexts} · heap ${heapNote}`));
    this.section("Parses", "(each root)");
    const rs = this.list("state-roots");
    const prog = programRoot(st.roots);
    for (const r of st.roots) {
      const li = el("li", "root");
      li.dataset.parse = r.parse;
      li.append(el("span", "parse", `parse ${r.parse}`), el("span", "production", r.production), el("span", "span", `[${r.lo}, ${r.hi})`), el("span", "how", r.kind));
      if (r === prog) {
        li.classList.add("program");
        li.title = "select it in the source";
        li.onclick = () => m.selectSpan(r.lo, r.hi);
      }
      rs.append(li);
    }
    this.section("Running SDOs' Parse Nodes", `(${st.evalNodes.length})`);
    const ns = this.list("state-sdos");
    for (const n of st.evalNodes) ns.append(el("li", "sdo", n));
    this.section("Arguments Lists passed", `(${st.passed.length})`);
    const ps = this.list("state-passed");
    for (const v of st.passed) ps.append(this.tree.node(`passed/${v.name}`, v));
    const host = el("details", "host");
    host.id = "state-host";
    host.open = this.hostOpen;
    host.ontoggle = () => (this.hostOpen = host.open);
    host.append(el("summary", "", "host / model"));
    const t = el("table");
    for (const [k, v] of Object.entries(st.host)) {
      const tr = el("tr");
      tr.append(el("td", "key", k), el("td", "value", v === null ? "none" : String(v)));
      t.append(tr);
    }
    host.append(t);
    this.root.append(host);
  }
}
