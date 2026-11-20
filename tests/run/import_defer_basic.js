// args: --bundle
// expect: throw: SyntaxError
// ECMA-262 as it stands has no `import defer` and no `import.defer()`: this is a SyntaxError.
// With proposal-defer-import-eval applied (branch proposal-defer-import-eval; the debugger's build
// "Proposal: import defer") it completes normally and prints:
//   [object Deferred Module]
//   main starts; heavy evaluates; read 42; read again 42
// proposal-defer-import-eval: `import defer * as heavy` loads and links heavy.mjs with the graph but evaluates it at the
// first read of an export (the namespace's [[Get]]: GetModuleExportsList, EvaluateModuleSync); %Symbol.toStringTag%
// is read without evaluating it (IsSymbolLikeNamespaceKey), and is "Deferred Module" (ModuleNamespaceCreate).
// JS_BUNDLE_MODULE:log.mjs
export const log = [];
// JS_BUNDLE_MODULE:heavy.mjs
import { log } from "./log.mjs";
log.push("heavy evaluates");
export const answer = 42;
// JS_BUNDLE_MODULE_ENTRYPOINT:main.mjs
import { log } from "./log.mjs";
import defer * as heavy from "./heavy.mjs";
log.push("main starts");
print(Object.prototype.toString.call(heavy));
log.push("read " + heavy.answer);
log.push("read again " + heavy.answer);
print(log.join("; "));
