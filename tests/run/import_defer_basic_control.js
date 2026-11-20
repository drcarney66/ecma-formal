// args: --bundle
// expect: normal: undefined
// print: [object Module]
// print: heavy evaluates; main starts; read 42; read again 42
// import_defer_basic.js without `defer`: heavy.mjs evaluates before main.mjs, and its namespace is a "Module".
// JS_BUNDLE_MODULE:log.mjs
export const log = [];
// JS_BUNDLE_MODULE:heavy.mjs
import { log } from "./log.mjs";
log.push("heavy evaluates");
export const answer = 42;
// JS_BUNDLE_MODULE_ENTRYPOINT:main.mjs
import { log } from "./log.mjs";
import * as heavy from "./heavy.mjs";
log.push("main starts");
print(Object.prototype.toString.call(heavy));
log.push("read " + heavy.answer);
log.push("read again " + heavy.answer);
print(log.join("; "));
