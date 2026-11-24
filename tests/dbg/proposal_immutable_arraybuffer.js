"use strict";
const ab = new ArrayBuffer(4);
new Uint8Array(ab).set([10, 20, 30, 40]);
const sliced = ab.sliceToImmutable(1, 3);
const moved = ab.transferToImmutable(6);
const view = new Uint8Array(moved);
let writeThrew = false;
try { view[0] = 99; } catch (e) { writeThrew = e instanceof TypeError; }
print([
  "slice=" + Array.from(new Uint8Array(sliced)).join(","),
  "detached=" + ab.detached,
  "immutable=" + moved.immutable,
  "writeThrew=" + writeThrew
].join(", "));
