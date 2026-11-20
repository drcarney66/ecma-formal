// expect: normal: "TypeError;1;1;9,NaN,NaN"
// The text since tc39/ecma262 PR #3979 (4feb0272b):
// %TypedArray%.prototype.with step 5's ToBigInt(value) runs a valueOf that
// shrinks the resizable buffer to one element; index 0 stays valid (step 7),
// but step 10.b reads *undefined* for k = 1, and step 10.c's
// TypedArraySetElement throws a TypeError at ToBigInt(undefined), which the
// method returns. The value is coerced once, and the source keeps its one
// element. On a Number TypedArray the same shrink gives NaN (ToNumber(undefined))
// for the elements past the new length, with no throw.
var out = [];
var rab = new ArrayBuffer(24, { maxByteLength: 24 });
var ta = new BigInt64Array(rab);
ta[0] = 1n; ta[1] = 2n; ta[2] = 3n;
var calls = 0;
try {
  ta.with(0, { valueOf() { calls++; rab.resize(8); return 9n; } });
  out.push("no error");
} catch (e) { out.push(e.constructor.name); }
out.push(calls);
out.push(ta.length);
var rab2 = new ArrayBuffer(24, { maxByteLength: 24 });
var fa = new Float64Array(rab2);
fa[0] = 1; fa[1] = 2; fa[2] = 3;
var r = fa.with(0, { valueOf() { rab2.resize(8); return 9; } });
out.push(Array.from(r).join(","));
out.join(";")
