// Flags: --bundle

// JS_BUNDLE_MODULE:lib/math.mjs
export function double(x) {
  return x * 2;
}
// JS_BUNDLE_MODULE:lib/show.mjs
import { double } from "./math.mjs";
export function show(x) {
  print(double(x));
}
// JS_BUNDLE_MODULE_ENTRYPOINT:main.mjs
import { show } from "./lib/show.mjs";
show(21);
