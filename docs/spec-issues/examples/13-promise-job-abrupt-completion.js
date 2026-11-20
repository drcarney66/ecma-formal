// §9.5 "The Abstract Closure must return a normal completion" against
// NewPromiseReactionJob 1.i "Return ? Call(promiseCapability.[[Resolve]], …)",
// with a capability whose resolve function throws (a species constructor).
// The second reaction has no handler: its Job's realm is null, yet it calls
// the program's resolve function (§9.5: such a job "does not evaluate
// ECMAScript code").
if (typeof print === "undefined") globalThis.print = console.log;
function Bad(executor) {
  executor(function (v) { print("resolve(" + v + ") called; it throws"); throw new Error("boom"); },
           function () {});
}
Bad[Symbol.species] = Bad;
var p = Promise.resolve(1);
p.constructor = Bad;
p.then(function (v) { print("handler " + v); return v; });
var q = Promise.resolve(2);
q.constructor = Bad;
q.then();   // no handler: the Job's realm is null
Promise.resolve(3).then(function () { print("a later Job runs"); });
