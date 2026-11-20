// expect: normal: undefined
// print: true,false,true,true
// print: true,false
// Property escapes over the typed Unicode property tables (refactor R11,
// findings F15-F17): a name and value, a lone General_Category value, a lone
// binary property, and a property of strings with the v flag.
print([/\p{Script=Latn}/u.test("a"), /\p{sc=Grek}/u.test("a"), /\p{Lu}/u.test("A"),
  /^\p{Emoji_Keycap_Sequence}$/v.test("#\uFE0F\u20E3")].join(","));
print([/\P{AHex}/u.test("g"), /\p{Any}/u.test("") ].join(","));
void 0;
