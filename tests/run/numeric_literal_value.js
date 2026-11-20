// expect: normal: "ok"
// The NumericValue of a NumericLiteral is computed in Lean from its exact MV:
// RoundMVResult for a DecimalLiteral (NonOctalDecimalIntegerLiteral `089`
// included), 𝔽(MV) for NonDecimalIntegerLiteral and LegacyOctalIntegerLiteral.
// Huge exponents finish without building 10^e.
var results = [
  1e999999999 === Infinity,
  1e-999999999 === 0,
  1 / -1e-999999999 === -Infinity,
  0e999999999 === 0,
  1e999999999999999999999999999999999999999999 === Infinity,
  1.5e-999999999999999999999999999999999999999999 === 0,
  0x10 === 16,
  0o17 === 15,
  0b1_0 === 2,
  017 === 15,
  089 === 89,
  08.5 === 8.5,
  1_000.5e1 === 10005,
  .5 === 0.5,
  0.1 + 0.2 !== 0.3,
  1234567890123456789012345 === Number("1234567890123456789012345"),
  0xFFFFFFFFFFFFFFFFFFFFFFFF === 79228162514264337593543950335,
  9007199254740993 === 9007199254740992,
  // 2^70 + 2^17 + 1, just above a midpoint: 𝔽(MV) (hex/octal) rounds up to 2^70 + 2^18,
  // while RoundMVResult's 20-digit option1 (...434400) rounds to 2^70.
  1180591620717411434497 === 1180591620717411303424,
  01180591620717411434497 === 1180591620717411303424,
  0x400000000000020001 === 1180591620717411565568,
  0200000000000000000400001 === 1180591620717411565568,
  2.4703282292062328e-324 === 5e-324,
  2.4703282292062327e-324 === 0,
  1.7976931348623158e308 === 1.7976931348623157e308,
  1.7976931348623159e308 === Infinity,
];
results.every(function (r) { return r; }) ? "ok" : "fail " + results.indexOf(false)
