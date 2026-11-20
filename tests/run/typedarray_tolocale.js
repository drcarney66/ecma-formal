// %TypedArray%.prototype.toLocaleString (§23.2.3.31) on a host without ECMA-402: Array's steps after
// ValidateTypedArray, with TypedArrayLength for the length and the host's separator ", ".
// expect: normal: "1, -2, 3||5, 0|0, 0|x1, x2|TypeError,TypeError,TypeError|0,toLocaleString"
var TA = Object.getPrototypeOf(Int8Array.prototype);
var tla = TA.toLocaleString;
function err(f) {
  try { f(); return "none"; } catch (e) { return e.constructor.name; }
}
var withLength = new Uint8Array(2);
Object.defineProperty(withLength, "length", { get: function () { throw 1; } });
var detached = new Uint8Array(new ArrayBuffer(2));
detached.buffer.transfer();
var saved = Number.prototype.toLocaleString;
Number.prototype.toLocaleString = function () { return "x" + this; };
var replaced = new Uint16Array([1, 2]).toLocaleString();
Number.prototype.toLocaleString = saved;
[
  new Int8Array([1, -2, 3]).toLocaleString(),
  new Float64Array(0).toLocaleString(),
  new BigInt64Array([5n, 0n]).toLocaleString(),
  withLength.toLocaleString(),
  replaced,
  [err(function () { tla.call([1, 2]); }), err(function () { tla.call(1); }),
    err(function () { detached.toLocaleString(); })].join(),
  [tla.length, tla.name].join()
].join("|")
