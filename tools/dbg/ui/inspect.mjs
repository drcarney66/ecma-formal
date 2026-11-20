// The inspector: the selected frame's scopes as lazy trees (tree.mjs) and the
// `stopped.spec.diff` summary (heap.mjs).

import { $ } from "./dom.mjs";
import { diffSummary } from "./heap.mjs";
import { Tree } from "./tree.mjs";

export class InspectPane {
  constructor(model) {
    this.model = model;
    this.root = $("inspect");
    this.diff = $("diff");
    this.tree = new Tree(model, new Set(["Slots"]));
    this.built = null;
    model.on("change", (what) => ["pause", "select", "scopes", "state"].includes(what) && this.render());
    this.render();
  }

  render() {
    const snap = this.model.state === "paused" ? this.model.snap : null;
    this.diff.textContent = "";
    if (snap) this.diff.append(diffSummary(this.model, snap.stopped.spec?.diff));
    const key = snap ? `${snap.gen}:${snap.selected}` : null;
    const scopes = snap?.scopes.get(snap.selected);
    if (key === this.built && (scopes || !snap)) return;
    this.root.textContent = "";
    this.built = scopes ? key : null;
    if (!scopes) return;
    for (const sc of scopes) this.root.append(this.tree.node(sc.name, { name: sc.name, value: "", variablesReference: sc.variablesReference }, true));
  }
}
