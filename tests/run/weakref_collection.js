// needs: $262.gc
// Not run: ecma-run's test host has no `$262.gc` and never collects (no
// Execution of §9.9.3 at a Job boundary); scripts/test262.py's HOST_LACKS
// has "gc" too.
// expect: normal: undefined
// print: true
// print: true
// print: true,undefined
// print: collected o
// Collection is the spec's, chosen by the host (refactor R24, DESIGN §16.20).
// On the test262 host, $262.gc() asks for a collection, which the host
// performs at the next Job boundary: after ClearKeptObjects, every value held
// only weakly and unreachable from the agent is collected (§9.9.3).
// wm.has(o, …) is true although its second argument drops o and asks for a
// collection: the collection waits for the boundary. There, o is held only by
// wm and fr, so the WeakMap entry is emptied and fr's cell is cleaned up in a
// cleanup Job (HostEnqueueFinalizationRegistryCleanupJob, §9.9.4.1), which
// runs after the promise Job enqueued before it. A WeakRef
// whose target is held only by it derefs to its target in the same Job and to
// undefined after the boundary; one whose target is live keeps it.
var wm = new WeakMap();
var o = {};
wm.set(o, 1);
var fr = new FinalizationRegistry(function (held) { print("collected " + held); });
fr.register(o, "o");
print(wm.has(o, (o = null, $262.gc())));
var kept = {};
var w = new WeakRef({});
var k = new WeakRef(kept);
print(typeof w.deref() === "object");
Promise.resolve().then(function () {
  print((k.deref() === kept) + "," + String(w.deref()));
});
void 0;
