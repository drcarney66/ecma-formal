// expect: normal: undefined
// print: 1,2,3|6|e|a,b|d0,d1|9|m|x
// Async functions and async generators on the frame machine (DESIGN §7): each
// Await suspends the body's context until a promise job resumes it; `for await`
// awaits each IteratorResult; an `await using` declaration awaits its
// [Symbol.asyncDispose] at the end of the block (DisposeResources §7.5.5); an
// async arrow's `super(await …)` binds the this value after its Await (the
// constructor itself returns before, without a this value: a ReferenceError).
var out = [];
async function* agen() { yield 1; yield await Promise.resolve(2); yield 3; }
async function collect() { var r = []; for await (var v of agen()) r.push(v); return r.join(); }
async function sum() { var s = 0; for (var i = 1; i <= 3; i++) s += await i; return s; }
async function caught() { try { await Promise.reject("e"); } catch (e) { return e; } }
async function syncIter() { var r = []; for await (var v of ["a", Promise.resolve("b")]) r.push(v); return r.join(); }
async function disposing() {
  var log = [];
  {
    await using x = { async [Symbol.asyncDispose]() { log.push("d0"); } };
    await using y = { [Symbol.dispose]() { log.push("d1"); } };
  }
  return log.reverse().join();
}
class Base { constructor(v) { this.v = v; } }
var pending;
class Derived extends Base { constructor() { pending = (async () => super(await 9))(); } }
async function superCall() {
  try { new Derived(); } catch (e) { if (!(e instanceof ReferenceError)) throw e; }
  return (await pending).v;
}
async function optionalAwait() { var o = { m(x) { return x; } }; return o?.m(await "m"); }
async function importOptions() { try { await import("x", await { with: 1 }); } catch (e) { return "x"; } }
Promise.all([collect(), sum(), caught(), syncIter(), disposing(), superCall(), optionalAwait(), importOptions()])
  .then(function (r) { print(r.join("|")); }, function (e) { print("rejected " + e); });
void 0;
