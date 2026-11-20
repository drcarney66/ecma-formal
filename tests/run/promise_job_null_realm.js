// expect: normal: undefined
// print: resolve 2
// print: later
// A reaction with no handler (q.then()) makes a Job whose realm is null
// (NewPromiseReactionJob steps 2–3), and its step 1.i still calls the
// capability's resolve function, here the program's: §9.5 says such a Job
// "does not evaluate ECMAScript code", a note the model does not read (an editorial
// report, docs/spec-issues/47). The function runs in its own realm.
function Spy(executor) {
  executor(function (v) { print("resolve " + v); }, function () {});
}
Spy[Symbol.species] = Spy;
var q = Promise.resolve(2);
q.constructor = Spy;
q.then();
Promise.resolve(3).then(function () {}).then(function () { print("later"); });
void 0;
