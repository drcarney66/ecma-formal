// args: --bundle
// expect: throw: TypeError
// import_defer_dynamic.js with `import()`: dep.mjs evaluates, its namespace exports `then`, so the promise resolves
// to "oops" through it, and `"then" in` a String throws.
// JS_BUNDLE_MODULE:dep.mjs
globalThis.order.push("dep evaluates");
export function then(resolve) { globalThis.order.push("then called"); resolve("oops"); }
export const x = 1;
// JS_BUNDLE_MODULE_ENTRYPOINT:main.mjs
globalThis.order = [];
const ns = await import("./dep.mjs");
order.push("promise settled");
order.push("then in ns: " + ("then" in ns));
order.push("x is " + ns.x);
print(order.join("; "));
