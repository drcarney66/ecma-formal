// expect: normal: undefined
// print: timed-out 4
// print: timed-out 1700000000007 1700000000011
// DoWait step 23's implementation-defined additionalTimeout is the host's
// choice (0 here) increased by the least amount that makes timeoutTime an
// integral Number value (Erratum
// AtomicsWaitAsyncTimeoutAssert, kept literal: with it the Assert of
// EnqueueAtomicsWaitAsyncTimeoutJob 1.b.ii holds, docs/spec-issues/09). A
// 0.7 ms wait times out at the next whole millisecond, also when the clock is
// so large that 𝔽 of the exact time would round down. The default host's clock
// moves 1 ms at each reading of the current time (Host.elapsed): DoWait reads
// 1, so [[TimeoutTime]] is 2 (1.7 rounded up); step 2 of
// EnqueueAtomicsWaitAsyncTimeoutJob reads 2 (a delay of 0), the Job 3 and the
// reaction's Date.now() 4. The second wait reads 5 and is due at
// 1700000000005; the third, after the Job's and Date.now()'s readings
// (…06, …07), reads …08, is due at …09, and its reaction reads …11.
var i32 = new Int32Array(new SharedArrayBuffer(16));
Atomics.waitAsync(i32, 0, 0, 0.7).value.then(function (v) {
  print(v + " " + Date.now());
  Atomics.waitAsync(i32, 1, 0, 1699999999999.5).value.then(function () {
    var t = Date.now();
    Atomics.waitAsync(i32, 2, 0, 0.7).value.then(function (w) {
      print(w + " " + t + " " + Date.now());
    });
  });
});
void 0;
