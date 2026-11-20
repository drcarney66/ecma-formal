// A synchronous Atomics.wait with a fractional timeout (§25.4.3.14, on an
// agent that can block): SuspendThisAgent wakes the agent at the first whole
// millisecond at which the current time is at least [[TimeoutTime]], so the
// current time stays a time value (§21.4.1.1; audit F093/F204) and
// toISOString's step 5 Assert holds.
// args: --can-block
// expect: normal: undefined
// print: timed-out,true,1970-01-01T00:00:00.004Z
var i32 = new Int32Array(new SharedArrayBuffer(8));
var r = Atomics.wait(i32, 0, 0, 0.5);
var now = Date.now();
print([r, Number.isInteger(now), new Date().toISOString()].join());
