// args: --host-seed 1
// expect: normal: undefined
// print: timed-out,true
// §9.5.6: HostEnqueueTimeoutJob performs its Job "after at least" its
// milliseconds (host law timeoutAfter). The seeded host, whose clock advances
// about 1 s per host call, moves it at least to a taken timeout Job's due
// time, so the Job of a 100 s wait reads a time at or past [[TimeoutTime]]:
// EnqueueAtomicsWaitAsyncTimeoutJob's Assert (1.b.ii) holds.
var ia = new Int32Array(new SharedArrayBuffer(8));
var before = Date.now();
Atomics.waitAsync(ia, 0, 0, 100000).value.then(function (v) {
  print([v, Date.now() - before >= 100000].join(","));
});
void 0;
