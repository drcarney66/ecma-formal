// args: --host-seed 1
// expect: normal: undefined
// print: pending
// A timeout Job whose due time is past the time value range (§21.4.1.1) is
// never taken by the seeded host (host law timeoutAfter, §9.5.6): the run
// ends with the waiter's promise pending.
var ia = new Int32Array(new SharedArrayBuffer(8));
Atomics.waitAsync(ia, 0, 0, 1e300).value.then(function (v) { print(v); });
print("pending");
void 0;
