// The console: what the program printed (`output`), the engine's stderr, the end of the
// run (`terminated`: outcome and exit code) and the engine's.

import { $, el } from "./dom.mjs";

export class ConsolePane {
  constructor(model) {
    this.model = model;
    this.root = $("console");
    this.shown = 0;
    this.output = null;
    $("clear-console").onclick = () => {
      this.root.textContent = "";
    };
    model.on("change", (what) => what === "output" && this.render());
  }

  render() {
    const out = this.model.output;
    if (out !== this.output) {
      this.output = out;
      this.shown = 0;
      if (out.length === 0) this.root.append(el("div", "session", "— new session —"));
    }
    for (; this.shown < out.length; this.shown++) {
      const { category, text } = out[this.shown];
      this.root.append(el("div", `out ${category}`, text.replace(/\n$/, "")));
    }
    this.root.scrollTop = this.root.scrollHeight;
  }
}
