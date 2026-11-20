// %TypedArray%.prototype methods: numeric sort (CompareTypedArrayElements),
// subarray sharing the buffer, from with a mapper, and iteration.
// expect: normal: "-0,0,1,2,NaN ; 9,2 ; 2,4,6 ; 5|6"
var f = new Float64Array([NaN, 2, 0, -0, 1]).sort();
var a = new Int16Array([1, 2, 3]);
a.subarray(0, 1)[0] = 9;
[Object.is(f[0], -0) ? "-0" + f.join().slice(1) : f.join(),
 a.subarray(0, 2).join(),
 Uint8Array.from([1, 2, 3], x => x * 2).join(),
 [...new Uint16Array([5, 6])].join("|")].join(" ; ")
