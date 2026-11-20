// EnqueueAtomicsWaitAsyncTimeoutJob 1.b.ii: "Assert: ℝ(timeOfJobExecution) ≥
// waiterRecord.[[TimeoutTime]]". With a fractional timeout and
// additionalTimeout 0, [[TimeoutTime]] is not a time value; a host whose clock
// has millisecond resolution may run the Job (after "at least" the step 4
// delay) at a time below it.
if (typeof print === "undefined") globalThis.print = console.log;
var ia = new Int32Array(new SharedArrayBuffer(8));
var t0 = Date.now();
var r = Atomics.waitAsync(ia, 0, 0, 0.7);
print(r.async);
r.value.then(function (v) { print(v + ", elapsed ≥ 0: " + (Date.now() - t0 >= 0)); });
// (node ends the process when only an Atomics.waitAsync timeout is pending)
if (typeof setTimeout === "function") setTimeout(function () {}, 50);
