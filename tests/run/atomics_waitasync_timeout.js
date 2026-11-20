// expect: normal: undefined
// print: true,object
// print: ok
// print: first
// print: timed-out,true
// The host schedules Jobs (refactor R28, DESIGN §16.25). Atomics.waitAsync
// with a finite timeout performs EnqueueAtomicsWaitAsyncTimeoutJob, whose Job
// HostEnqueueTimeoutJob schedules "after at least milliseconds milliseconds".
// The default host takes the oldest Job that is due: the promise Jobs
// enqueued after the timeout Jobs run first; then it waits on its clock, and
// the first timeout Job resolves its promise with "timed-out" at a current
// time 10 ms later. The second waiter is notified before its timeout, so its
// promise has "ok", and its timeout Job finds no waiter (step 1.b).
var ia = new Int32Array(new SharedArrayBuffer(16));
var before = Date.now();
var r = Atomics.waitAsync(ia, 0, 0, 10);
print([r.async, typeof r.value].join(","));
r.value.then(function (v) { print([v, Date.now() - before >= 10].join(",")); });
var r2 = Atomics.waitAsync(ia, 1, 0, 50);
Atomics.notify(ia, 1);
r2.value.then(function (v) { print(v); });
Promise.resolve().then(function () { print("first"); });
void 0;
