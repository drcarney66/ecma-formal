// expect: normal: [object #N]
// print: ok

function assertEq(actual, expected, msg) {
  if (!Object.is(actual, expected)) {
    throw new Error((msg || "mismatch") + ": got " + String(actual) + ", expected " + String(expected));
  }
}

// 1. AbortController & AbortSignal lifecycle + addAbortCallback + Symbol.dispose
const ac = new AbortController();
const sig = ac.signal;
assertEq(sig.aborted, false, "initially not aborted");
assertEq(sig.reason, undefined, "initial reason undefined");

const log = [];
const reg1 = sig.addAbortCallback(() => log.push("cb1:" + sig.reason));
const reg2 = sig.addAbortCallback(() => log.push("cb2"));
reg2.remove();
{
  using _scoped = sig.addAbortCallback(() => log.push("scoped"));
}
ac.abort("cancelled!");
assertEq(sig.aborted, true, "aborted true");
assertEq(sig.reason, "cancelled!", "reason set");
assertEq(log.join(","), "cb1:cancelled!", "only active callback ran");

// 2. Default AbortError when reason omitted + throwIfAborted
const sDefault = AbortSignal.abort();
assertEq(sDefault.aborted, true, "AbortSignal.abort() is aborted");
assertEq(sDefault.reason.name, "AbortError", "default AbortError name");
let threwReason = null;
try { sDefault.throwIfAborted(); } catch (e) { threwReason = e; }
assertEq(threwReason, sDefault.reason, "throwIfAborted throws reason");

// 3. Dependent signals via AbortSignal.any
const cA = new AbortController();
const cB = new AbortController();
const dep = AbortSignal.any([cA.signal, cB.signal]);
let depFired = 0;
dep.addAbortCallback(() => { depFired++; });
cB.abort("from-B");
cA.abort("from-A");
assertEq(dep.aborted, true, "dependent signal aborted");
assertEq(dep.reason, "from-B", "dependent signal takes first abort reason");
assertEq(depFired, 1, "dependent callback runs once");

// 4. Atomics.waitAsync with AbortSignal
const sab = new SharedArrayBuffer(4);
const i32 = new Int32Array(sab);
const waitAc = new AbortController();
const res = Atomics.waitAsync(i32, 0, 0, { signal: waitAc.signal });
assertEq(res.async, true, "waitAsync pending");
waitAc.abort("stop-wait");
res.value.then(
  () => { throw new Error("expected rejection"); },
  (err) => {
    assertEq(err, "stop-wait", "waitAsync rejected with abort reason");
    print("ok");
  }
);
