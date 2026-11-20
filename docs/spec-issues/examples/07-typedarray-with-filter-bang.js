// %TypedArray%.prototype.with 10.c and filter 11.a: "Perform !
// TypedArraySetElement(…)" where ToBigInt(undefined) throws a TypeError.
if (typeof print === "undefined") globalThis.print = console.log;
var rab = new ArrayBuffer(16, { maxByteLength: 16 });
var ta = new BigInt64Array(rab);
try {
  ta.with(0, { valueOf() { rab.resize(8); return 0n; } });
  print("with: no exception");
} catch (e) { print("with: " + e.constructor.name); }
var rab2 = new ArrayBuffer(16, { maxByteLength: 16 });
var tb = new BigInt64Array(rab2);
var calls = 0;
try {
  tb.filter(function () { calls++; rab2.resize(8); return true; });
  print("filter: no exception");
} catch (e) { print("filter: " + e.constructor.name + " after " + calls + " calls"); }
