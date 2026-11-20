// args: --module-dir tests/run/modules
// expect: normal: undefined
// print: 1 Module 1
// import() evaluates its specifier, then loads, links and evaluates the module
// (EvaluateImportCall §13.3.10.2, ContinueDynamicImport §13.3.10.3); the namespace object
// fulfils the Promise, whose reaction runs as a Job after the Script.
var log = [];
import((log.push(1), "./lib.mjs")).then(function (ns) {
  ns.increment();
  print(log.join(",") + " " + ns[Symbol.toStringTag] + " " + ns.counter);
});
void 0;
