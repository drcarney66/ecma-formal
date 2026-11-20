// args: --bundle
// expect: normal: undefined
// print: m
// print: n true
// print: 3
// print: TypeError
// A d8 bundle's dynamic imports: from the bundle's script before the entrypoint (against the root),
// from the entrypoint, and from a module (against its own key: dir/m.mjs's `./n.mjs` is
// /dir/n.mjs, the module the script loaded); a JSON module; a name the bundle lacks is a TypeError.
// JS_BUNDLE_SCRIPT
var fromScript = import("dir/n.mjs");
// JS_BUNDLE_MODULE:dir/m.mjs
export const x = "m";
export function load(s) { return import(s); }
// JS_BUNDLE_MODULE:dir/n.mjs
export const y = "n";
// JS_BUNDLE_MODULE:data.json
{"k": 3}
// JS_BUNDLE_MODULE_ENTRYPOINT:main.mjs
var sn;
fromScript
  .then(function (n) { sn = n; return import("./dir/m.mjs"); })
  .then(function (m) { print(m.x); return m.load("./n.mjs"); })
  .then(function (n) { print(n.y + " " + (n === sn)); return import("./data.json", { with: { type: "json" } }); })
  .then(function (j) { print(j.default.k); return import("./missing.mjs"); })
  .then(function () { print("loaded"); }, function (e) { print(e.constructor.name); });
