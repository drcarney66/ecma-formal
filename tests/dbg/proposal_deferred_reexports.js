// JS_BUNDLE_MODULE:log.mjs
export const events = [];
// JS_BUNDLE_MODULE:heavy.mjs
import { events } from "./log.mjs";
events.push("heavy");
export const x = 99;
// JS_BUNDLE_MODULE:barrel.mjs
import { events } from "./log.mjs";
export defer { x } from "./heavy.mjs";
events.push("barrel");
// JS_BUNDLE_MODULE_ENTRYPOINT:main.mjs
import { events } from "./log.mjs";
import * as barrel from "./barrel.mjs";
print("after barrel import: " + events.join(","));
const v = barrel.x;
print("after reading barrel.x=" + v + ": " + events.join(","));
