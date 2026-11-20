// parseInt and parseFloat (§19.2.4–5), Array.prototype.flat / flatMap
// (§23.1.3.13–14) and the toLocaleString methods.
// Array.prototype.toLocaleString joins with LocalizedListSeparator ( ) (sec-localizedlistseparator,
// an implementation-defined host operation): its law (Ecma.Host.LocaleLaws.listSeparator)
// asks only for a String; the fixed host answers ", " (Engine/Host/Core.lean), the
// spec's own example, so `[1, 2, null, 3]` gives "1, 2, , 3".
// expect: normal: "255|-0|NaN|8|3.14|-Infinity|0.5|NaN|1e+21|1,2,3,4,5|1,1,2,2|1, 2, , 3|7"
[
  parseInt("  0xff"),
  1 / parseInt("-0") === -Infinity ? "-0" : "+0",
  parseInt("z", 35),
  parseInt("10", 8),
  parseFloat("3.14abc"),
  parseFloat("-Infinityx"),
  parseFloat(".5e"),
  parseFloat("e5"),
  parseInt("1000000000000000000000"),
  [1, [2, [3, [4, [5]]]]].flat(Infinity).join(),
  [1, 2].flatMap(function (x) { return [x, x]; }).join(),
  [1, 2, null, 3].toLocaleString(),
  (7).toLocaleString()
].join("|")
