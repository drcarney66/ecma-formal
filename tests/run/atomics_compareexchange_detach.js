// Atomics.compareExchange (§25.4.6) when step 1's ToIndex(index) detaches the
// buffer: step 3 reads [[ArrayBufferData]], which is null, steps 4–5 still
// coerce expectedValue and replacementValue, and step 6 (RevalidateAtomicAccess
// → ValidateTypedArrayBounds) throws a TypeError. Also for a BigInt64Array, and
// with an expectedValue that throws first (its abrupt completion propagates).
// expect: normal: undefined
// print: index,expected,replacement,TypeError
// print: index,expected,replacement,TypeError
// print: index,expected,SyntaxError
function run(ta, ab, expected, replacement) {
  var log = [];
  try {
    Atomics.compareExchange(ta,
      { valueOf() { log.push("index"); ab.transfer(); return 0; } },
      { valueOf() { log.push("expected"); if (expected === "throw") throw new SyntaxError(); return expected; } },
      { valueOf() { log.push("replacement"); return replacement; } });
    log.push("no throw");
  } catch (e) { log.push(e.constructor.name); }
  print(log.join());
}
var ab1 = new ArrayBuffer(16); run(new Int32Array(ab1), ab1, 0, 1);
var ab2 = new ArrayBuffer(16); run(new BigInt64Array(ab2), ab2, 0n, 1n);
var ab3 = new ArrayBuffer(16); run(new Int32Array(ab3), ab3, "throw", 1);
void 0;
