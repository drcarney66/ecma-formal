// needs: $262.gc
// Not run: ecma-run's test host has no `$262.gc` and never collects (no
// Execution of §9.9.3 at a Job boundary); scripts/test262.py's HOST_LACKS
// has "gc" too.
// expect: normal: undefined
// print: job
// print: collected a
// print: collected b
// One target registered twice in one FinalizationRegistry. Execution step 1.b
// (§9.9.3) empties one cell of the registry per Execution; the value stays
// not live (a cell's [[WeakRefTarget]] does not make it live, §9.9.2), so the
// test262 host performs Execution again until no cell holds it, and each
// registration gets its callback.
var fr = new FinalizationRegistry(function (held) { print("collected " + held); });
var o = {};
fr.register(o, "a");
fr.register(o, "b");
o = null;
$262.gc();
Promise.resolve().then(function () { print("job"); });
void 0;
