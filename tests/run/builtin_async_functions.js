// expect: normal: undefined
// print: 1,2,3|2,4|a,b|true|,d
// Built-in async functions (§10.3.3 step 10) run on the frame machine:
// Array.fromAsync over an async iterable, an array-like object with a mapper
// that returns promises, and a sync iterable; a rejected element rejects the
// promise; AsyncDisposableStack.prototype.disposeAsync awaits the disposers.
async function* gen() { yield 1; yield Promise.resolve(2); yield 3; }
var log = [];
var stack = new AsyncDisposableStack();
stack.defer(async function () { log.push("d"); });
Promise.all([
  Array.fromAsync(gen()),
  Array.fromAsync({ length: 2, 0: 1, 1: 2 }, function (v) { return Promise.resolve(v * 2); }),
  Array.fromAsync(new Set(["a", "b"])),
  Array.fromAsync([Promise.reject(new Error("x"))]).then(function () { return false; }, function () { return true; }),
  stack.disposeAsync().then(function (v) { return [v, log.join()]; })
]).then(function (r) { print(r.map(function (x) { return String(x); }).join("|")); },
        function (e) { print("rejected " + e); });
void 0;
