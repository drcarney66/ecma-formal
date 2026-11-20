// A StringLiteral "__proto__" is not a computed key, so it is still the proto setter
// (§13.2.5.6 step 3).
// expect: normal: 3
({"__proto__": {x: 3}}).x
