// %TypedArray%.prototype.filter step 11.b, as tc39/ecma262 PR #3979 (4feb0272b)
// writes it: a callback that detaches the buffer, or shrinks a
// resizable one, makes the later kValues undefined (TypedArrayGetElement step 1);
// when they are kept, TypedArraySetElement's ToBigInt(undefined) throws a
// TypeError, after every callback has run. The earlier `!` (726ec8a42) made it an
// assertion failure; test262 (callbackfn-{detachbuffer,shrink}-kept-undefined.js)
// requires the TypeError.
// expect: normal: "TypeError,3,1n|undefined|undefined ; TypeError,3,1n|2n|undefined ; 3,1,NaN"
function run(ta, act) {
  var seen = [];
  var error;
  try {
    ta.filter(function (value, index) {
      if (index === 0) act();
      seen.push(String(value) + (typeof value === "bigint" ? "n" : ""));
      return true;
    });
  } catch (e) {
    error = e.constructor.name;
  }
  return [error, seen.length, seen.join("|")].join();
}
var detached = new BigInt64Array([1n, 2n, 3n]);
var rab = new ArrayBuffer(24, { maxByteLength: 24 });
var shrunk = new BigInt64Array(rab);
shrunk[0] = 1n; shrunk[1] = 2n; shrunk[2] = 3n;
// A Number TypedArray converts undefined to NaN (ToNumber), so nothing throws.
var numbers = new Float64Array([1, 2, 3]);
var kept = numbers.filter(function (value, index) {
  if (index === 0) numbers.buffer.transfer();
  return true;
});
[run(detached, function () { detached.buffer.transfer(); }),
 run(shrunk, function () { rab.resize(16); }),
 [kept.length, kept[0], kept[1]].join()].join(" ; ")
