// DoWait 28.a–31: a synchronous Atomics.wait that times out. Literal text:
// it returns "ok" (the [[Result]] of step 26) and its Waiter Record stays in
// the WaiterList; the second wait then fails AddWaiter step 2's Assert, and
// Atomics.notify counts a waiter that is not waiting.
// (Needs an agent that can block: node, bun, d8, the SpiderMonkey shell.)
if (typeof print === "undefined") globalThis.print = console.log;
var ia = new Int32Array(new SharedArrayBuffer(4));
print(Atomics.wait(ia, 0, 0, 0));
print(Atomics.wait(ia, 0, 0, 1));
print(Atomics.notify(ia, 0));
