// Atomics.wait on an agent that can block (§25.4.3.14, SuspendThisAgent
// §25.4.3.11): with one agent nothing notifies the waiter, so it wakes when
// the host's clock reaches its timeout time. Erratum DoWaitSyncTimeout: the
// woken waiter's [[Result]] is "timed-out" and it leaves the WaiterList, so a
// second wait on the same location does not fail AddWaiter step 2's Assert
// and a later Atomics.notify finds no waiter.
// args: --can-block
// expect: normal: undefined
// print: timed-out,timed-out,true,true,0 ; not-equal
var i32 = new Int32Array(new SharedArrayBuffer(8));
var t0 = Date.now();
var first = Atomics.wait(i32, 0, 0, 10);
var t1 = Date.now();
var second = Atomics.wait(i32, 0, 0, 5);
var t2 = Date.now();
var notified = Atomics.notify(i32, 0);
Atomics.store(i32, 1, 3);
print([first, second, t1 - t0 >= 10, t2 - t1 >= 5, notified].join() + " ; " + Atomics.wait(i32, 1, 0, 10));
void 0;
