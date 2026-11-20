// expect: normal: undefined
// print: function,2,undefined
// print: sync
// print: promise
// print: t0
// print: t5
// print: t10,true
// setTimeout (the test host's global) performs HostEnqueueTimeoutJob of a Job that calls its callback:
// the promise Jobs run first, then each timeout Job once its delay has passed; a negative delay is 0.
var before = Date.now();
print([typeof setTimeout, setTimeout.length, typeof setTimeout(function () { print("t0"); }, -3)].join(","));
setTimeout(function () { print("t5"); }, 5);
setTimeout(function () { print(["t10", Date.now() - before >= 10].join(",")); }, 10);
Promise.resolve().then(function () { print("promise"); });
print("sync");
