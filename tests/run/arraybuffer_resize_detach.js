// A length-tracking TypedArray follows a resizable ArrayBuffer (§10.4.5.13),
// and a transferred buffer is detached (ArrayBufferCopyAndDetach, §25.1.3.3).
// expect: normal: "4,8,2 ; true,0,0,8"
var ab = new ArrayBuffer(4, { maxByteLength: 8 });
var u8 = new Uint8Array(ab);
var s = [u8.length];
ab.resize(8);
s.push(u8.length, new Uint32Array(ab).length);
var ab2 = ab.transfer();
[s.join(), [ab.detached, ab.byteLength, u8.length, ab2.byteLength].join()].join(" ; ")
