// args: --bundle
// expect: normal: undefined
// print: b sees a: function
// print: a sees b: 2
// print: main sees 1 1
// A d8 bundle (`--bundle`) whose modules import each other: lib/b.mjs's `../a.mjs` and a.mjs's
// `./lib/b.mjs` resolve to the bundle's keys /a.mjs and /lib/b.mjs, and the cycle evaluates b first.
// JS_BUNDLE_MODULE:a.mjs
import { b, useA } from "./lib/b.mjs";
export function a() { return 1; }
print("a sees b: " + (b + useA()));
// JS_BUNDLE_MODULE:lib/b.mjs
import { a } from "../a.mjs";
export const b = 1;
export function useA() { return a(); }
print("b sees a: " + typeof a);
// JS_BUNDLE_MODULE_ENTRYPOINT:main.mjs
import { a } from "a.mjs";
import { b } from "./lib/../lib/b.mjs";
print("main sees " + a() + " " + b);
