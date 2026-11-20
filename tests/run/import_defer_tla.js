// args: --bundle
// expect: throw: SyntaxError
// ECMA-262 as it stands has no `import defer` and no `import.defer()`: this is a SyntaxError.
// With proposal-defer-import-eval applied (branch proposal-defer-import-eval; the debugger's build
// "Proposal: import defer") it completes normally and prints:
//   before access: b, e, d, a
//   after access: b, e, d, a, f, c
// proposal-defer-import-eval, the README's graph: c is deferred, but its dependency d has top-level await, so d and
// its dependency e evaluate with the graph (InnerModuleEvaluation, GatherAsynchronousTransitiveDependencies); f and
// c wait for the first read of c's namespace.
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
import defer * as c from "./c.mjs";
order.push("a");
print("before access: " + order.join(", "));
c.value;
print("after access: " + order.join(", "));
