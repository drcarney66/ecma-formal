// The implementation-approximated Math functions (§21.3.2): the special
// values are exact; js-run approximates the rest with the C library (Float).
// expect: normal: "0.8414709848078965|2.356194490192345|5|3|1.5707963267948966|3|-0|NaN|Infinity|1|-Infinity|0"
[
  Math.sin(1),
  Math.atan2(1, -1),
  Math.hypot(3, 4),
  Math.cbrt(27),
  Math.atan(Infinity),
  Math.log10(1000),
  Object.is(Math.tan(-0), -0) ? "-0" : "no",
  Math.acos(2),
  Math.cosh(-Infinity),
  Math.exp(-0),
  Math.log(0),
  Math.hypot(-0, 0)
].join("|")
