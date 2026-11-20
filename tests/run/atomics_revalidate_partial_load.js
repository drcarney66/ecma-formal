// expect: normal: undefined
// print: RangeError
// RevalidateAtomicAccess checks the element's last byte against the buffer length
// (steps 4-6, tc39/ecma262 PR #3926, 5e0f8b33): a length-tracking Int32Array over a
// resizable buffer that the coercion shrinks to 6 bytes has byteIndex 4, whose element
// ends at byte 7 >= 6, so Atomics.load throws a RangeError before sec-getvaluefrombuffer runs.
var rab = new ArrayBuffer(16, { maxByteLength: 16 });
var ta = new Int32Array(rab);
var shrink = { valueOf() { rab.resize(6); return 1; } };
try { Atomics.load(ta, shrink); print("no error"); } catch (e) { print(e.constructor.name); }
