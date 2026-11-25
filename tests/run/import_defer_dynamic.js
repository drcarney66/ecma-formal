// args: --bundle
// expect: normal: undefined
// print: promise settled; then in ns: false; dep evaluates; x is 1
// proposal-defer-import-eval: `import.defer()` settles with a deferred namespace without evaluating the module
// (ContinueDynamicImport, GatherAsynchronousTransitiveDependencies finds nothing); "then" is not an export of a
// deferred namespace (GetModuleNamespace), so the promise's resolution does not evaluate it either
// (IsSymbolLikeNamespaceKey); reading `x` does.
// JS_BUNDLE_MODULE:dep.mjs
globalThis.order.push("dep evaluates");
export function then(resolve) { globalThis.order.push("then called"); resolve("oops"); }
export const x = 1;
// JS_BUNDLE_MODULE_ENTRYPOINT:main.mjs
globalThis.order = [];
const ns = await import.defer("./dep.mjs");
order.push("promise settled");
order.push("then in ns: " + ("then" in ns));
order.push("x is " + ns.x);
print(order.join("; "));
