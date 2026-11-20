// The JS stack pane: one frame for each execution context, the running one first
// (`stackTrace {view: "js"}`), each with its function's name, its JS position and, for
// a built-in's context, the built-in. The frame that holds the selected spec frame is
// marked; selecting one selects its innermost spec frame and shows its position.

import { $, el } from "./dom.mjs";

export class JsStackPane {
  constructor(model) {
    this.model = model;
    this.list = $("jsstack");
    model.on("change", (what) => ["pause", "jsFrames", "select", "state"].includes(what) && this.render());
    this.render();
  }

  render() {
    const snap = this.model.state === "paused" ? this.model.snap : null;
    this.list.textContent = "";
    const frames = snap?.jsFrames ?? [];
    const holds = snap ? this.model.jsFrameOf(snap.selected) : null;
    for (const f of frames) {
      const li = el("li", "frame");
      li.dataset.id = f.id;
      if (f === holds) li.classList.add("selected");
      li.append(el("span", "name", f.name));
      if (f.line > 0) li.append(el("span", "pos", `${f.source?.name ?? "source"}:${f.line}:${f.column}`));
      else li.append(el("span", "pos", "no position"));
      if (f.inBuiltin !== undefined) li.append(el("span", "builtin", f.inBuiltin));
      const { lo, hi } = f.spec.frames;
      li.title = `spec frames ${lo}–${hi - 1}${f.spec.site ? ` (pushed: ${f.spec.site})` : ""}`;
      li.onclick = () => this.model.selectJsFrame(f.id);
      this.list.append(li);
    }
    $("jsstack-count").textContent = snap?.jsFrames ? `${frames.length}` : "";
  }
}
