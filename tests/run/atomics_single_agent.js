// Atomics in one agent (§25.4): read-modify-write returns the old value,
// notify finds no waiters, wait throws on an agent that cannot block, and
// waitAsync's waiter (WaiterList Records) is resolved with "ok" by notify, or
// is "not-equal" / "timed-out" without waiting.
// expect: normal: undefined
// print: 0,5,0 ; 12 ; TypeError ; true,false,false,1 ; ok,not-equal,timed-out
var i32 = new Int32Array(new SharedArrayBuffer(8));
var s = [Atomics.add(i32, 0, 5), Atomics.compareExchange(i32, 0, 5, 7), Atomics.notify(i32, 0)].join();
Atomics.or(i32, 1, 12);
var w;
try { Atomics.wait(i32, 0, 7, 0); } catch (e) { w = e.name; }
var waiting = Atomics.waitAsync(i32, 0, 7);
var notEqual = Atomics.waitAsync(i32, 0, 0);
var timedOut = Atomics.waitAsync(i32, 0, 7, 0);
var notified = Atomics.notify(i32, 0);
var head = [s, Atomics.load(i32, 1), w,
  [waiting.async, notEqual.async, timedOut.async, notified].join()].join(" ; ");
waiting.value.then(function (v) { print(head + " ; " + [v, notEqual.value, timedOut.value].join()); });
void 0;
