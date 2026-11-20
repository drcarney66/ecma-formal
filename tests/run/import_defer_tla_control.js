// args: --bundle
// expect: normal: undefined
// print: before access: b, e, f, d, c, a
// print: after access: b, e, f, d, c, a
// import_defer_tla.js without `defer`: every module evaluates before a.
// JS_BUNDLE_MODULE:order.mjs
export const order = [];
// JS_BUNDLE_MODULE:b.mjs
import { order } from "./order.mjs";
order.push("b");
// JS_BUNDLE_MODULE:e.mjs
import { order } from "./order.mjs";
order.push("e");
// JS_BUNDLE_MODULE:d.mjs
import { order } from "./order.mjs";
import "./e.mjs";
await 0;
order.push("d");
// JS_BUNDLE_MODULE:f.mjs
import { order } from "./order.mjs";
order.push("f");
// JS_BUNDLE_MODULE:c.mjs
import { order } from "./order.mjs";
import "./d.mjs";
import "./f.mjs";
order.push("c");
export let value = 2;
// JS_BUNDLE_MODULE_ENTRYPOINT:a.mjs
import { order } from "./order.mjs";
import "./b.mjs";
import * as c from "./c.mjs";
order.push("a");
print("before access: " + order.join(", "));
c.value;
print("after access: " + order.join(", "));
