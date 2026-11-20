// Patterns: group names compare by CapturingGroupName (escapes resolved),
// quantifier bounds of any size, the ClassEscape `c` AsciiLetter in a class.
// expect: normal: undefined
// print: xx xx
// print: SyntaxError
// print: true true
// print: SyntaxError
// print: true false a__b
// print: true
function t(f) { try { print(f()); } catch (e) { print(e.name); } }
t(() => new RegExp("(?<\\u0061>.)\\k<a>", "u").exec("xx")[0] + " " + /(?<a>.)\k<a>/.exec("xx")[0]);
t(() => new RegExp("(?<a>.)(?<\\u0061>.)", "u"));
t(() => new RegExp("^a{0,9007199254740992}$").test("aa") + " " + /^a{0,99999999999999999999999}$/.test("aaa"));
t(() => new RegExp("a{99999999999999999999999,9}"));
t(() => /[\cA-\cZ]/.test("\x05") + " " + /[\cA-\cZ]/.test("B") + " " + "a\r\nb".replace(/[\cJ\cM]/g, "_"));
t(() => /[\cA]/u.test("\x01"));
