// Link of a Synthetic Module Record: InnerModuleLinking 1.a calls it for each
// importer, and each call gives the module a new environment whose bindings
// are undefined until InnerModuleEvaluation evaluates it again. other.mjs
// imports probe.mjs before j.json, so probe.mjs runs between the two.
if (typeof print === "undefined") globalThis.print = console.log;
import j from "./j.json" with { type: "json" };
export function readJ() { return j; }
print("main sees " + JSON.stringify(j));
import("./other.mjs").then(function () { print("after other: " + JSON.stringify(j)); },
                           function (e) { print("rejected: " + e); });
