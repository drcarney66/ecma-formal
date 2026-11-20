// expect: stop: sortError sec-setvalueinbuffer#0 4
// args: --erratum AllocateSharedArrayBufferByteLengthStore=literal
// A growable SharedArrayBuffer (Erratum AllocateSharedArrayBufferByteLengthStore): the
// literal step passes a Shared Data Block to SetValueInBuffer, which takes a buffer object.
var b = new SharedArrayBuffer(1, { maxByteLength: 4 });
b.grow(2);
b.byteLength;
