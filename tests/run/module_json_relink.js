// module: yes
// args: --module-dir tests/run/modules
// expect: normal: undefined
// print: main sees 1
// print: probe sees undefined
// print: after other: 1
// Link of a Synthetic Module Record (§16.2.1.8.4.4) runs for every importer
// that is linked (InnerModuleLinking 1.a) and gives the module a new
// environment whose bindings are undefined until it is evaluated again. The
// second importer (modules/relink_other.mjs) imports modules/relink_probe.mjs
// before the JSON module, so the probe runs between the second Link and the
// second evaluation and reads undefined through this module's import. Kept
// literal (Erratum SyntheticModuleLinkResets, docs/spec-issues/15): no
// test262 test evaluates a module in between. Engines print 1.
import j from "./relink.json" with { type: "json" };
export function readJ() { return j; }
print("main sees " + j.a);
import("./relink_other.mjs").then(function () { print("after other: " + j.a); },
  function (e) { print("rejected " + e); });
