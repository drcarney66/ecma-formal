// AllocateSharedArrayBuffer step 9.c stores the length with SetValueInBuffer(_byteLengthBlock_, …), passing a
// Shared Data Block where SetValueInBuffer takes an ArrayBuffer or SharedArrayBuffer.
if (typeof print === "undefined") globalThis.print = console.log;
var sab = new SharedArrayBuffer(4, { maxByteLength: 16 });
print(sab.growable + " " + sab.byteLength + " " + sab.maxByteLength);
sab.grow(8);
print(sab.byteLength + " " + new Int32Array(sab).length);
