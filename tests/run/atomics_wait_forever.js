// expect: stop: blocked formal-agent-interleave#0 6.a
// A synchronous Atomics.wait with no timeout (realTimeout +∞, DoWait step 9)
// on the only agent: nothing can call NotifyWaiter, so SuspendThisAgent step 7
// never wakes it and the run never ends. The model gives a run that never ends
// as `outOfFuel` at every fuel (not `unsupported`).
// args: --can-block
var i32 = new Int32Array(new SharedArrayBuffer(16));
Atomics.wait(i32, 0, 0);
