// module: yes
// args: --checked --module-dir tests/run/modules
// expect: normal: undefined
// print: x,y|1|2
import * as ns from "./diamond_a.mjs";
print(Object.keys(ns).join(",") + "|" + ns.x + "|" + ns.y);
