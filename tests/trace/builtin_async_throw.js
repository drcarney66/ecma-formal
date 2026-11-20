// A built-in async function that throws before its first Await
// (Array.fromAsync with a mapper that is not callable, its step 3.a): the
// throw completes the function's steps, which BuiltinCallOrConstruct (§10.3.3) receives
// as result (step 10.b.ii) and returns (10.b.iii). Both twins call the
// built-in, which runs on the frame machine (`Machine.builtinStart` under
// `Machine.guarded`), so the expect line is the check: without the routing the
// throw skips the frame that traces these steps.
// sections: sec-builtincallorconstruct sec-array.fromasync
// expect: sec-builtincallorconstruct 10.b.iii. Return Completion(result).
function plain() {
  Math.max();
  Array.fromAsync([1], 5);
  Math.min();
}
function* gen() {
  Math.max();
  Array.fromAsync([1], 5);
  Math.min();
}
