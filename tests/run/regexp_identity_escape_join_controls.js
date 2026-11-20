// Erratum IdentityEscapeJoinControls, at its test262 reading: without the
// u or v flag, `\` U+200C (ZWNJ) and `\` U+200D (ZWJ) are IdentityEscapes,
// as test262's language/literals/regexp/S7.8.5_A1.4_T2.js and
// S7.8.5_A2.4_T2.js require, although Unicode 15.1 made both UnicodeIDContinue.
// ecma-run's default host does not support §B.1.2, so this is the main grammar:
// the other UnicodeIDContinue code points (`a`, U+00B7) stay SyntaxErrors, and
// U+200B and U+200E (not ID_Continue) are IdentityEscapes. The u and v flags
// allow neither. The characters are invisible: the patterns are built with
// fromCharCode.
// expect: normal: undefined
// print: U+200C: literal true, class true, a-literal true, RegExp true, u SyntaxError, v SyntaxError
// print: U+200D: literal true, class true, a-literal true, RegExp true, u SyntaxError, v SyntaxError
// print: U+200B: literal true, class true, a-literal true, RegExp true, u SyntaxError, v SyntaxError
// print: U+200E: literal true, class true, a-literal true, RegExp true, u SyntaxError, v SyntaxError
// print: U+61: literal SyntaxError, class SyntaxError, a-literal SyntaxError, RegExp SyntaxError, u SyntaxError, v SyntaxError
// print: U+B7: literal SyntaxError, class SyntaxError, a-literal SyntaxError, RegExp SyntaxError, u SyntaxError, v SyntaxError
function t(f) { try { return f(); } catch (e) { return e.name; } }
for (var cu of [0x200C, 0x200D, 0x200B, 0x200E, 0x61, 0xB7]) {
  var ch = String.fromCharCode(cu), src = "\\" + ch;
  print("U+" + cu.toString(16).toUpperCase() + ": " + [
    "literal " + t(() => { var re = eval("/" + src + "/"); return re.source === src && re.test(ch) && !re.test("x"); }),
    "class " + t(() => eval("/[" + src + "]/").test(ch)),
    "a-literal " + t(() => eval("/a" + src + "/").test("a" + ch)),
    "RegExp " + t(() => new RegExp(src).exec("x" + ch)[0] === ch),
    "u " + t(() => new RegExp(src, "u")),
    "v " + t(() => new RegExp(src, "v")),
  ].join(", "));
}
