// expect: normal: 2
// A growable SharedArrayBuffer (Erratum AllocateSharedArrayBufferByteLengthStore): the
// test262 reading stores the byte length in its Shared Data Block, which grow reads.
var b = new SharedArrayBuffer(1, { maxByteLength: 4 });
b.grow(2);
b.byteLength;
