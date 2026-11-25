// expect: normal: undefined
// print: ok

"use strict";

function assertThrows(fn, Err) {
  let threw = false;
  try { fn(); } catch (e) {
    threw = true;
    if (!(e instanceof Err)) throw new Error("wrong error: " + e);
  }
  if (!threw) throw new Error("expected throw");
}

const ab = new ArrayBuffer(4);
new Uint8Array(ab).set([10, 20, 30, 40]);
if (ab.immutable !== false) throw new Error("mutable buffer immutable=false");

const sliced = ab.sliceToImmutable(1, 3);
if (sliced.immutable !== true) throw new Error("sliceToImmutable immutable=true");
if (sliced.byteLength !== 2) throw new Error("sliceToImmutable byteLength");
if (ab.detached !== false) throw new Error("sliceToImmutable keeps source attached");

const view = new Uint8Array(sliced);
if (view[0] !== 20 || view[1] !== 30) throw new Error("sliceToImmutable bytes");
const desc = Object.getOwnPropertyDescriptor(view, "0");
if (desc.writable !== false || desc.configurable !== false) throw new Error("immutable descriptor");

assertThrows(() => { view[0] = 99; }, TypeError);
assertThrows(() => { view.fill(0); }, TypeError);
assertThrows(() => { view.sort(); }, TypeError);
assertThrows(() => { new DataView(sliced).setUint8(0, 1); }, TypeError);
assertThrows(() => { sliced.transfer(); }, TypeError);
assertThrows(() => { sliced.transferToImmutable(); }, TypeError);

const imm = ab.transferToImmutable(6);
if (ab.detached !== true) throw new Error("transferToImmutable detaches source");
if (imm.immutable !== true || imm.byteLength !== 6) throw new Error("transferToImmutable result");
const iv = new Uint8Array(imm);
if (iv[0] !== 10 || iv[3] !== 40 || iv[5] !== 0) throw new Error("transferToImmutable contents");

print("ok");
