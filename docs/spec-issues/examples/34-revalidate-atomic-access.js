// RevalidateAtomicAccess step 4 checks only the element's first byte: a coercion that shrinks a
// length-tracking view into its last element (bytes 4..7, 6 left) passes it.
if (typeof print === "undefined") globalThis.print = console.log;
function test(name, f) {
  var rab = new ArrayBuffer(16, { maxByteLength: 16 });
  var ta = new Int32Array(rab);
  var shrink = { valueOf() { rab.resize(6); return 1; } };
  try { print(name + ": returned " + f(ta, shrink)); }
  catch (e) { print(name + ": " + e.constructor.name); }
}
test("Atomics.store", (ta, s) => Atomics.store(ta, 1, s));
test("Atomics.add", (ta, s) => Atomics.add(ta, 1, s));
test("Atomics.load", (ta, s) => Atomics.load(ta, s));
test("Atomics.compareExchange", (ta, s) => Atomics.compareExchange(ta, 1, 0, s));
