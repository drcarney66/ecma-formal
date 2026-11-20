// The current time is a time value (§21.4.1.1: "a finite integral Number"),
// whatever the timeouts of Atomics.waitAsync (audit F014/F035/F093/F204).
// The host's clock moves in whole milliseconds, so after the timeout Job of a
// 0.5 ms wait, Date.now(), new Date() and toISOString (whose step 5 asserts an
// integral time value) see integral values, and new Date() agrees with
// new Date(Date.now()). The default host's clock starts at the epoch and moves
// a millisecond at each reading of the current time (Host.elapsed), so the
// values are exact: DoWait reads 1 (so [[TimeoutTime]] is 2: 1.5 rounded up,
// Erratum AtomicsWaitAsyncTimeoutAssert), EnqueueAtomicsWaitAsyncTimeoutJob
// reads 2 (a delay of 0, not negative: Erratum
// AtomicsWaitAsyncTimeoutNegativeDelay), the timeout Job 3, and the reaction
// 4 and 5.
// expect: normal: undefined
// print: timed-out,4,4,true,true,1970-01-01T00:00:00.004Z,5,true
var ia = new Int32Array(new SharedArrayBuffer(16));
Atomics.waitAsync(ia, 0, 0, 0.5).value.then(function (v) {
  var d = new Date();
  var t = d.getTime();
  print([v, t, d.valueOf(), Number.isInteger(t), d.getUTCMilliseconds() === t % 1000, d.toISOString(),
    Date.now(), new Date(Date.now()).getTime() > t].join());
});
void 0;
