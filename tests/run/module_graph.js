// module: yes
// args: --module-dir tests/run/modules
// expect: normal: undefined
// A module graph: live bindings, a default export, a namespace re-export.
import Point, { counter, increment, self } from "./lib.mjs";
increment();
if (counter !== 1 || self.counter !== 1) throw new Error("live binding");
if (new Point(2).x !== 2) throw new Error("default export");
