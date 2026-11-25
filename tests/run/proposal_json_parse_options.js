// expect: normal: undefined
// print: ok

function assertEq(actual, expected, msg) {
  if (!Object.is(actual, expected)) {
    throw new Error((msg || "mismatch") + ": got " + String(actual) + ", expected " + String(expected));
  }
}

// 1. freeze: true -> freezes objects & arrays recursively, AND defaults nullPrototypeObjects to true!
const imm = JSON.parse('{"a":[1,{"b":2}],"__proto__":{"x":9}}', { freeze: true });
assertEq(Object.isFrozen(imm), true, "root frozen");
assertEq(Object.getPrototypeOf(imm), null, "root null proto by default with freeze: true");
assertEq(Object.isFrozen(imm.a), true, "array frozen");
assertEq(Object.getPrototypeOf(imm.a), Array.prototype, "array keeps Array.prototype");
assertEq(Object.isFrozen(imm.a[1]), true, "nested object frozen");
assertEq(Object.getPrototypeOf(imm.a[1]), null, "nested object null proto");
assertEq(Object.getPrototypeOf(imm.__proto__), null, "__proto__ own property null proto");
assertEq(imm.__proto__.x, 9, "__proto__ own data property");

// 2. freeze: true, nullPrototypeObjects: false -> frozen with Object.prototype
const immProto = JSON.parse('{"k":1}', { freeze: true, nullPrototypeObjects: false });
assertEq(Object.isFrozen(immProto), true, "frozen with Object.prototype");
assertEq(Object.getPrototypeOf(immProto), Object.prototype, "Object.prototype kept");

// 3. nullPrototypeObjects: true (freeze defaults to false) -> extensible null-prototype objects
const nullOnly = JSON.parse('{"nested":{"v":3},"arr":[1]}', { nullPrototypeObjects: true });
assertEq(Object.isFrozen(nullOnly), false, "not frozen");
assertEq(Object.isExtensible(nullOnly), true, "extensible");
assertEq(Object.getPrototypeOf(nullOnly), null, "root null proto");
assertEq(Object.getPrototypeOf(nullOnly.nested), null, "nested null proto");
assertEq(Object.getPrototypeOf(nullOnly.arr), Array.prototype, "arr keeps Array.prototype");

// 4. GetBooleanOption ~reject~: non-boolean values throw TypeError
for (const bad of [{ freeze: 1 }, { freeze: "true" }, { nullPrototypeObjects: 0 }, { nullPrototypeObjects: null }]) {
  let threw = false;
  try {
    JSON.parse("{}", bad);
  } catch (e) {
    threw = e instanceof TypeError;
  }
  assertEq(threw, true, "non-boolean option rejected");
}

// 5. Callable reviver with properties is treated as reviver, NOT options
function reviver(k, v) { return typeof v === "number" ? v * 10 : v; }
reviver.freeze = "not-a-boolean";
const rev = JSON.parse('{"n":4}', reviver);
assertEq(rev.n, 40, "callable reviver invoked");
assertEq(Object.getPrototypeOf(rev), Object.prototype, "callable reviver keeps Object.prototype");

print("ok");
