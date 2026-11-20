// p.then() with no handler: the reaction Job's realm is null (HostEnqueuePromiseJob's note: no user code
// runs), yet NewPromiseReactionJob step 1.i calls the derived promise's resolve function.
if (typeof print === "undefined") globalThis.print = console.log;
function Species(executor) {
  executor(function (v) { print("resolve(" + v + ") called by the null-realm Job"); }, function () {});
}
Species[Symbol.species] = Species;
var q = Promise.resolve(2);
q.constructor = Species;
q.then();
Promise.resolve(3).then(function () { print("a later Job runs"); });
