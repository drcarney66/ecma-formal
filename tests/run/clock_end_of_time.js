// expect: stop: implLimit ? ?
// The current time is never past the last time value (8.64 × 10^15 ms,
// §21.4.1.1): a timeout Job due after it would need a current time the spec
// has no time value for, so the host's wait for it stops the run at the
// implementation limit (DESIGN §16.7), as a String past its length bound does
// (audit F014/F035: before, Date.now() was 9e15 and new Date() held a
// [[DateValue]] that is not a time value).
var ia = new Int32Array(new SharedArrayBuffer(16));
Atomics.waitAsync(ia, 0, 0, 9e15).value.then(function (v) { print(v + " " + Date.now()); });
