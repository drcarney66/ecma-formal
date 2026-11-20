// Number::multiply step 6 and the sign of an exact zero product.
// Literal step 6: 𝔽(0) is +0, so 1/(+0 * -5) is +Infinity.
// IEEE 754-2019 (the clause's description): -0, so -Infinity.
if (typeof print === "undefined") globalThis.print = console.log;
print(String(1 / (0 * -5)));   // +0 × -5
print(String(1 / (-5 * 0)));   // -5 × +0
print(String(1 / (0 * 5)));    // +0 × 5 (both readings: Infinity)
print(String(Object.is(-5 * 0, -0)));
