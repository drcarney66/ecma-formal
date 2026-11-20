// needs: shared blocks whose cost does not grow with their size
// expect: normal: "0;7;7;9;3;12;5;0"
// shared_memory_events.js with a 1 MiB SharedArrayBuffer in place of its
// 1 KiB one: R15 (DESIGN §16.11) made a block's creation one compressed
// ~init~ event, so that neither its creation nor the shared operations after
// it grow with its size. Not run: they do now. Measured alone (2026-11-19, on a
// loaded machine): creating the block takes 4.1 s at 1 MiB (its 2^20 ~init~
// events; the Data Block itself is one value), and the whole program 2.1 s at
// 1 KiB, 92 s at 64 KiB and over 120 s at 1 MiB (the suite's limit is 60 s):
// each later shared read scans the event list. A plain store, an
// Atomics.add (a read-modify-write), a compareExchange that fails and one
// that succeeds, a copy from a shared into a shared block (per-byte events)
// and a grow each read the bytes of the last write.
var out = [];
var big = new SharedArrayBuffer(2 ** 20);
var bv = new Uint8Array(big);
out.push(bv[2 ** 20 - 1]);
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
