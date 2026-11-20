// args: --bundle
// expect: normal: undefined
// print: slow starts
// print: slow ends
// print: entry sees 7
// print: entry ends
// A d8 bundle whose anonymous entrypoint imports a module with top-level await: the entrypoint
// runs after the dependency's evaluation settles.
// JS_BUNDLE_MODULE:slow.mjs
print("slow starts");
await Promise.resolve();
print("slow ends");
export const v = 7;
// JS_BUNDLE_MODULE_ENTRYPOINT
import { v } from "slow.mjs";
print("entry sees " + v);
await null;
print("entry ends");
