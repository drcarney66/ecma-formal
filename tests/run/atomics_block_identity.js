// expect: normal: undefined
// print: 0,0,8
// print: 0,0
// print: 12
// Data Blocks have identity (refactor R5, finding F1). Atomics.compareExchange
// step 3 names buffer.[[ArrayBufferData]] before the coercions of steps 4-5;
// a coercion that resizes the buffer puts a new Data Block into the slot
// (ArrayBuffer.prototype.resize step 14), and step 14 reads and writes the
// block of step 3. So the exchange does not reach ta[0], and the value read
// is the old block's.
var ab = new ArrayBuffer(4, { maxByteLength: 8 });
var ta = new Int32Array(ab);
var old = Atomics.compareExchange(ta, 0, { valueOf: function () { ab.resize(8); return 0; } }, 5);
print([old, ta[0], ab.byteLength].join(","));
// The variant: after the resize, ta[0] is 7 in the new block, but the
// comparison reads the old block, whose element is 0.
var ab2 = new ArrayBuffer(4, { maxByteLength: 8 });
var ta2 = new Int32Array(ab2);
var read = Atomics.compareExchange(ta2, 0,
  { valueOf: function () { ab2.resize(8); ta2[0] = 7; return 7; } }, 5);
print([read, ta2[0] - 7].join(","));
// SharedArrayBuffer.prototype.grow: the compare-exchange loop of step 12 on
// [[ArrayBufferByteLengthData]].
var sab = new SharedArrayBuffer(4, { maxByteLength: 16 });
sab.grow(12);
print(String(sab.byteLength));
void 0;
