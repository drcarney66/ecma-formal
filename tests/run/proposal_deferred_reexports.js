// args: --bundle
// expect: normal: undefined
// print: barrel evaluated: log=barrel
// print: read re-exported x=99: log=barrel,heavy
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
import * as b from "./barrel.mjs";
print("barrel evaluated: log=" + events.join(","));
const val = b.x;
print("read re-exported x=" + val + ": log=" + events.join(","));
