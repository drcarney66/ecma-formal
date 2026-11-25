// The step pane: the selected frame's algorithm, sec-id, step path and text, its kind,
// its Parse Node, and the link to the live draft (D12: the text shown is the pinned one).
// Below, the algorithm's listing (`specAlgorithm`): its steps nested, an erratum's
// reading under its step, the frame's step highlighted and scrolled to. A step's gutter
// toggles a spec breakpoint there (secId#idx, path), as the breakpoints pane lists it;
// a reading's steps have none (a breakpoint's path is the algorithm's).

import { $, el } from "./dom.mjs";

export const specLink = (secId) => `https://tc39.es/ecma262/#${secId}`;

export class StepPane {
  constructor(model) {
    this.model = model;
    this.root = $("step");
    this.shown = null;
    model.on("change", (what) =>
      ["pause", "frames", "select", "state", "listing", "breakpoints", "notation"].includes(what) && this.render());
    this.render();
  }

  render() {
    const f = this.model.state === "paused" ? this.model.frame() : null;
    const spectec = this.model.notation === "spectec";
    this.root.textContent = "";
    if (!f) {
      this.shown = null;
      return;
    }
    const s = f.spec;
    const head = el("div", "alg");
    head.append(el("span", "name", f.name), el("span", "path", ` step ${s.path}`));
    const id = el("div", "secid");
    const a = el("a", "", `${s.secId}${s.idx ? `#${s.idx}` : ""}`);
    a.href = specLink(s.secId);
    a.target = "_blank";
    a.rel = "noopener";
    a.title = "the live draft; it may differ from the pinned text";
    id.append(a);
    if (s.reading) id.append(el("span", "reading", ` erratum ${s.reading}`));
    const kind = [s.kind, ...(s.flags ?? [])].join(" ");
    id.append(el("span", "kind", ` ${kind}${s.run ? `, run ${s.run}` : ""}`));
    const stepText = spectec && s.spectec ? s.spectec : s.text;
    this.root.append(head, id, el("div", spectec ? "steptext spectec" : "steptext", `${s.path}. ${stepText}`));
    if (s.node) this.root.append(el("div", "node", `${s.node.production} [${s.node.lo}, ${s.node.hi})`));
    const l = this.model.listing(s.secId, s.idx ?? 0);
    if (l === undefined) this.root.append(el("div", "listing-note", "loading the algorithm…"));
    else if (l === null) this.root.append(el("div", "listing-note", "no listing"));
    else this.listing(l, s, spectec);
  }

  // The listing `l`, with the step of the frame's spec `s` current.
  listing(l, s, spectec = false) {
    const head = el("div", "signature", spectec && l.spectecHead ? l.spectecHead : `${l.name}(${l.params.join(", ")})`);
    if (!spectec && l.production) head.append(el("span", "production", ` ${l.production}`));
    const ol = el("ol", spectec ? "listing spectec" : "listing");
    let current = null;
    const add = (steps) => {
      for (const st of steps) {
        const li = el("li", "lstep");
        li.dataset.path = st.path;
        if (st.reading) {
          li.dataset.reading = st.reading;
          li.classList.add("reading");
        }
        const gutter = el("span", "gutter", "");
        gutter.style.marginRight = `${st.depth * 1.2}em`;
        if (!st.reading) {
          const on = this.model.config.breakpoints.some((bp, i) =>
            this.model.breakpointAt(bp, this.model.bpStatus[i], l.secId, l.idx) && (bp.path ?? "1") === st.path);
          gutter.textContent = on ? "●" : "";
          if (on) li.classList.add("bp");
          gutter.title = on ? "remove the breakpoint" : "break at this step";
          gutter.onclick = () => this.model.toggleBreakpoint(l.secId, l.idx, st.path);
        }
        const stText = spectec && st.spectec ? st.spectec : st.text;
        li.append(gutter, el("span", "spath", `${st.path}.`), el("span", "stext", ` ${stText}`));
        if ((st.reading ?? null) === (s.reading ?? null) && st.path === s.path) {
          li.classList.add("current");
          current = li;
        }
        ol.append(li);
        add(st.steps ?? []);
      }
    };
    add(l.steps);
    this.root.append(head, ol);
    const at = `${l.secId}#${l.idx} ${s.reading ?? ""} ${s.path} ${this.model.snap?.gen}:${this.model.snap?.selected}`;
    if (current && at !== this.shown) current.scrollIntoView?.({ block: "nearest" });
    this.shown = at;
  }
}
