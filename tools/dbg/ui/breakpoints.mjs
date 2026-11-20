// The breakpoints pane: the program's line breakpoints (set in the source pane's gutter)
// with where they resolved, spec breakpoints (an algorithm by sec-id, sec-id#idx or name,
// and a step path, else its first step) with what the engine made of them (verified and
// the algorithms they resolved to, or why not), and the exception filters. The
// configuration (these, the line breakpoints by program, the program and stopOnEntry) is
// kept in a Storage (localStorage) under a build's key (builds.mjs storageKey; KEY by default) and sent at
// every session's start.

import { $, el } from "./dom.mjs";

const KEY = "ecma-dbg";
// The key an earlier page saved under: read once, then moved to KEY.
const OLD_KEY = "esl-dbg-ui";

// The saved configuration, or {}.
export function loadConfig(storage, key = KEY) {
  try {
    let saved = storage.getItem(key);
    if (saved === null && key === KEY) {
      saved = storage.getItem(OLD_KEY);
      if (saved !== null) {
        storage.setItem(KEY, saved);
        storage.removeItem(OLD_KEY);
      }
    }
    const c = JSON.parse(saved ?? "{}");
    return c && typeof c === "object" ? c : {};
  } catch {
    return {};
  }
}

export function saveConfig(storage, config, key = KEY) {
  const { program, breakpoints, lineBreakpoints, filters, stopOnEntry } = config;
  try {
    storage.setItem(key, JSON.stringify({ program, breakpoints, lineBreakpoints, filters, stopOnEntry }));
  } catch {}
}

// A Storage in memory (the self-test's).
export class MemoryStorage {
  constructor() {
    this.m = new Map();
  }
  getItem(k) {
    return this.m.has(k) ? this.m.get(k) : null;
  }
  setItem(k, v) {
    this.m.set(k, String(v));
  }
  removeItem(k) {
    this.m.delete(k);
  }
}

export class BreakpointsPane {
  constructor(model, storage, key = KEY) {
    this.model = model;
    this.storage = storage;
    this.key = key;
    this.list = $("breakpoints");
    this.filters = $("filters");
    const add = () => {
      const alg = $("bp-alg").value.trim();
      const path = $("bp-path").value.trim();
      if (!alg) return;
      this.model.setBreakpoints([...this.model.config.breakpoints, path ? { alg, path } : { alg }]);
      $("bp-alg").value = "";
      $("bp-path").value = "";
    };
    $("bp-add").onclick = add;
    for (const id of ["bp-alg", "bp-path"]) $(id).onkeydown = (e) => e.key === "Enter" && add();
    model.on("change", (what) => {
      if (["breakpoints", "filters", "program", "config"].includes(what)) saveConfig(storage, model.config, key);
      if (what === "breakpoints" || what === "state" || what === "program") this.renderBreakpoints();
      if (what === "filters") this.renderFilters();
    });
    this.renderBreakpoints();
    this.renderFilters();
  }

  renderBreakpoints() {
    this.list.textContent = "";
    const live = this.model.session !== null;
    const lines = this.model.lineBreakpoints();
    lines.forEach((bp, i) => {
      const st = this.model.lineStatus[i];
      const li = el("li", "bp line-bp");
      const mark = !live || !st || st.message === "pending" ? "pending" : st.verified ? "verified" : "unverified";
      li.classList.add(mark);
      li.append(el("span", "mark", mark === "verified" ? "●" : mark === "pending" ? "○" : "✗"));
      li.append(el("span", "alg", `line ${bp.line}`), el("span", "path", bp.column ? `:${bp.column}` : ""));
      if (live && st) li.append(el("span", "status", st.verified ? ` → ${st.line}:${st.column}` : ` ${st.message ?? "not verified"}`));
      const rm = el("button", "remove", "×");
      rm.title = "remove";
      rm.onclick = () => this.model.setLineBreakpoints(lines.filter((_, j) => j !== i));
      li.append(rm);
      this.list.append(li);
    });
    this.model.config.breakpoints.forEach((bp, i) => {
      const st = this.model.bpStatus[i];
      const li = el("li", "bp");
      const mark = !live || !st ? "pending" : st.verified ? "verified" : "unverified";
      li.classList.add(mark);
      li.append(el("span", "mark", mark === "verified" ? "●" : mark === "pending" ? "○" : "✗"));
      li.append(el("span", "alg", bp.alg), el("span", "path", bp.path ? ` ${bp.path}` : " (first step)"));
      if (live && st) li.append(el("span", "status", st.verified ? ` → ${(st.resolved ?? []).join(", ")}` : ` ${st.message ?? "not verified"}`));
      const rm = el("button", "remove", "×");
      rm.title = "remove";
      rm.onclick = () => this.model.setBreakpoints(this.model.config.breakpoints.filter((_, j) => j !== i));
      li.append(rm);
      this.list.append(li);
    });
  }

  renderFilters() {
    this.filters.textContent = "";
    const on = this.model.config.filters;
    this.model.filters().forEach((f, i) => {
      const label = el("label", "filter");
      const box = el("input");
      box.type = "checkbox";
      box.dataset.filter = f.filter;
      box.checked = on.includes(f.filter);
      box.onchange = () => {
        const next = this.model.filters().map((x) => x.filter).filter((x) => (x === f.filter ? box.checked : on.includes(x)));
        this.model.setFilters(next);
      };
      label.append(box, ` ${f.label}`);
      const st = this.model.filterStatus[on.indexOf(f.filter)];
      if (box.checked && st && !st.verified) label.append(el("span", "status", " (not available)"));
      this.filters.append(label);
    });
  }
}
