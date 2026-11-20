// expect: normal: "0;7;7;9;3;12;5;0"
// Shared-memory events (refactor R15, DESIGN §16.11). The shared-block
// operations append their memory-model events, and a read of shared memory
// is ChooseSharedRead: the bytes of the last write in agent-order. A fresh
// SharedArrayBuffer's bytes read back as 0 (its ~init~ event). The block is
// 1 KiB: the operations' cost grows with it (shared_memory_large_block.js
// keeps the 1 MiB program, not run). A plain store, an
// Atomics.add (a read-modify-write), a compareExchange that fails and one
// that succeeds, a copy from a shared into a shared block (per-byte events)
// and a grow each read the bytes of the last write.
var out = [];
var big = new SharedArrayBuffer(2 ** 10);
var bv = new Uint8Array(big);
out.push(bv[2 ** 10 - 1]);
var sab = new SharedArrayBuffer(8, { maxByteLength: 16 });
var ta = new Int32Array(sab);
ta[0] = 5;
out.push(Atomics.add(ta, 0, 2) + 2);
out.push(Atomics.compareExchange(ta, 0, 1, 100));
Atomics.compareExchange(ta, 0, 7, 9);
out.push(Atomics.load(ta, 0));
var u8 = new Uint8Array(sab);
u8[4] = 3;
out.push(u8.slice(4, 5)[0]);
sab.grow(12);
out.push(sab.byteLength);
var ta2 = new Int32Array(sab);
ta2[2] = 5;
u8.set(new Uint8Array(sab, 8, 1), 1);
out.push(new Uint8Array(sab)[1]);
out.push(new Uint8Array(sab)[11]);
out.join(";")
