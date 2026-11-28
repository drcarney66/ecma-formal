// The spec stack pane: the frames, innermost first, grouped by the run they belong to,
// each with its algorithm, step path, step text and source line. Selecting one drives
// the step and inspector panes; the frames of the JS frame that holds it are marked, and
// it is scrolled to. More frames load on demand.

import { $, el } from "./dom.mjs";

export class StackPane {
  constructor(model) {
    this.model = model;
    this.list = $("stack");
    this.more = $("more-frames");
    this.more.onclick = () => this.model.moreFrames();
    model.on("change", (what) =>
      ["pause", "frames", "jsFrames", "select", "state", "notation"].includes(what) && this.render(what));
    this.render();
  }

  render(what) {
    const snap = this.model.state === "paused" ? this.model.snap : null;
    const spectec = this.model.notation === "spectec";
    this.list.textContent = "";
    const frames = snap?.frames ?? [];
    const js = snap ? this.model.jsFrameOf(snap.selected) : null;
    let run = null;
    for (const f of frames) {
      if (f.spec.run !== run) {
        run = f.spec.run;
        this.list.append(el("li", "run", run === 0 ? "run 0 (the script)" : `run ${run}`));
      }
      const li = el("li", "frame");
      li.dataset.id = f.id;
      if (f.id === snap.selected) li.classList.add("selected");
      if (js && js.spec.frames.lo <= f.id && f.id < js.spec.frames.hi) li.classList.add("jsrange");
      li.append(el("span", "name", f.name), el("span", "path", f.spec.path));
      if (f.line > 0) li.append(el("span", "pos", `${f.source?.name ?? "source"}:${f.line}`));
      const fText = spectec && f.spec.spectec ? f.spec.spectec : f.spec.text;
      li.append(el("div", spectec ? "text spectec" : "text", fText));
      li.title = `${f.spec.secId} ${f.spec.path}: ${fText}`;
      li.onclick = () => this.model.selectFrame(f.id);
      this.list.append(li);
    }
    const total = snap?.totalFrames ?? 0;
    this.more.hidden = !snap || frames.length >= total;
    this.more.textContent = `more frames (${frames.length} of ${total})`;
    $("stack-count").textContent = snap && snap.totalFrames !== null ? `${total}` : "";
    if (what === "select") this.list.querySelector(".selected")?.scrollIntoView({ block: "nearest" });
  }
}
