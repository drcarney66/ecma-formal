// module: yes
// args: --module-dir tests/run/modules
// expect: normal: undefined
// print: 1,2 x true 1
// print: true
// print: TypeError
// print: SyntaxError
// The test host supports the "type" import attribute: `type: "json"` loads
// ParseJSONModule's record, one per specifier and type; another type is a
// TypeError, and no type parses the file as a Module.
import data from "./data.json" with { type: "json" };
import * as ns from "./data.json" with { type: "json" };
print(data.a.join(",") + " " + data.b + " " + (ns.default === data) + " " + Object.keys(ns).length);
import("./data.json", { with: { type: "json" } })
  .then(function (m) { print(m.default === data); return import("./data.json", { with: { type: "css" } }); })
  .then(function () { print("loaded"); }, function (e) { print(e.constructor.name); return import("./data.json"); })
  .then(function () { print("loaded"); }, function (e) { print(e.constructor.name); });
