// expect: normal: "true,false,true,true,false,true,true,true"
// Property escapes (§22.2.2.9, UnicodeMatchProperty and UnicodeMatchPropertyValue,
// Unicode 17.0.0): a General_Category value alone or with gc=, a Script and a
// Script_Extensions value, a binary property and its complement \P, and a
// binary property of strings with the v flag (a keycap sequence is one element).
[/^\p{Lu}+$/u.test("ABC"), /^\p{Lu}$/u.test("a"), /^\p{gc=Nd}+$/u.test("0123"),
 /^\p{Script=Greek}$/u.test("α"), /^\P{AHex}$/u.test("f"), /^\p{scx=Hira}$/u.test("ー"),
 /^\p{Emoji_Keycap_Sequence}$/v.test("1️⃣"), /^[\p{L}--\p{Lu}]$/v.test("x")].join()
