// expect: stop: assertFailed sec-jobs -
// NewPromiseReactionJob 1.i returns `? Call(promiseCapability.[[Resolve]], …)`;
// with a species constructor whose resolve throws, the Job returns a throw
// completion, which §9.5 says a Job must not. No test262 test makes a
// reaction Job's resolving function throw; the default reading is the text
// as written (Erratum PromiseJobAbruptCompletion), so the run
// stops. (Engine hosts differ: node goes on silently; the SpiderMonkey shell
// and Bun, with JavaScriptCore, report the throw and go on.)
function Bad(executor) {
  executor(function () { throw new Error("boom"); }, function () {});
}
Bad[Symbol.species] = Bad;
var p = Promise.resolve(1);
p.constructor = Bad;
p.then(function (v) { print("handler " + v); return v; });
Promise.resolve(3).then(function () { print("a later Job"); });
