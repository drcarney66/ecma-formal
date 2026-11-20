// expect: normal: "RangeError;TypeError;16"
// Refinement returns (refactor R19, DESIGN §16.15). Atomics.store coerces the
// value (a valueOf that shrinks the resizable buffer) after
// ValidateAtomicAccess; RevalidateAtomicAccess step 2 revalidates the bounds
// and step 4 compares the byte index with the record's
// [[CachedBufferByteLength]], which the record's type now guarantees is not
// ~detached~ (the old code read it with a default of 0). A DataView getter on a
// buffer that its index's valueOf shrinks throws a TypeError at GetViewValue's
// IsViewOutOfBounds step.
var out = [];
var rab = new ArrayBuffer(16, { maxByteLength: 16 });
var ta = new Int32Array(rab);
try {
  Atomics.store(ta, 3, { valueOf() { rab.resize(8); return 1; } });
  out.push("no error");
} catch (e) { out.push(e.constructor.name); }
var rab2 = new ArrayBuffer(16, { maxByteLength: 16 });
var dv = new DataView(rab2, 8);
try {
  dv.getInt8({ valueOf() { rab2.resize(4); return 0; } });
  out.push("no error");
} catch (e) { out.push(e.constructor.name); }
out.push(new Int32Array(new ArrayBuffer(16)).byteLength);
out.join(";")
