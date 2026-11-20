// Integer, clamped, binary16/32/64 and BigInt element conversions
// (NumericToRawBytes and RawBytesToNumeric, §25.1.3.14 and §25.1.3.17).
// expect: normal: "1,2,44,127 ; 0,255,2,254 ; 1.100000023841858 ; 65504,0.333251953125,Infinity ; -9223372036854775808"
[new Int8Array([1, 2, 300, -129]).join(),
 new Uint8ClampedArray([-5, 300, 2.5, 253.5]).join(),
 new Float32Array([1.1])[0],
 new Float16Array([65519, 1/3, 65520]).join(),
 new BigInt64Array([2n ** 63n])[0]].join(" ; ")
