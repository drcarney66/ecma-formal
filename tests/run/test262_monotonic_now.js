// The test262 host's `$262.agent.monotonicNow()` (INTERPRETING.md, "Monotonic
// Clock") is the current time, which only advances; the three Atomics.waitAsync
// tests that use it with one agent (audit F256) run. The other $262.agent
// functions stop with `unsupported` (one agent).
// expect: normal: undefined
// print: true,true
var a = $262.agent.monotonicNow();
var b = $262.agent.monotonicNow();
print([typeof a === "number", b > a].join());
