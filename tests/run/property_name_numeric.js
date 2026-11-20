// expect: normal: "ok"
// PropName and the Evaluation of a LiteralPropertyName : NumericLiteral are
// ! ToString(NumericValue), computed in Lean (RoundMVResult and
// Number::toString with the host's choices), not by the frontend.
var k = function (o) { return Object.keys(o)[0]; };
class C { 1.5e300() {} static 0x1F() {} get 1e-7() { return 1; } }
var d = Object.getOwnPropertyDescriptor(C.prototype, "1e-7");
var results = [
  k({1e21: 0}) === "1e+21",
  k({0.000001: 0}) === "0.000001",
  k({1e-7: 0}) === "1e-7",
  k({0x10: 0}) === "16",
  k({0o17: 0}) === "15",
  k({0b1_0: 0}) === "2",
  k({1n: 0}) === "1",
  k({0x1Fn: 0}) === "31",
  k({1_000.5: 0}) === "1000.5",
  k({.5: 0}) === "0.5",
  k({5.: 0}) === "5",
  k({1e999: 0}) === "Infinity",
  k({123456789012345678901234567890: 0}) === "1.2345678901234568e+29",
  C.prototype["1.5e+300"].name === "1.5e+300",
  C[31].name === "31",
  d.get.name === "get 1e-7",
  ({1.0: "a"})[1] === "a",
  // A NumericLiteral key is never "__proto__": a literal named 1 is an own property.
  Object.getPrototypeOf({1: null}) === Object.prototype,
  // Destructuring reads the key the same way.
  (function () { var {1e21: x} = {"1e+21": 7}; return x; })() === 7,
];
results.every(function (r) { return r; }) ? "ok" : "fail " + results.indexOf(false)
