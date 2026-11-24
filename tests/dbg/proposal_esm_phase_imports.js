// JS_BUNDLE_MODULE:dep.js
export let runs = 0;
runs++;
export const answer = 42;
// JS_BUNDLE_MODULE_ENTRYPOINT:main.js
import source depSrc from "./dep.js";
const dynSrc = await import.source("./dep.js");
const ns1 = await import(depSrc);
const ns2 = await import("./dep.js");
print([
  depSrc[Symbol.toStringTag],
  "sameSource=" + (depSrc === dynSrc),
  "sameNs=" + (ns1 === ns2),
  "runs=" + ns1.runs,
  "answer=" + ns1.answer
].join(", "));
