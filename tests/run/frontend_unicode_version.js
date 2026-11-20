// Identifiers are classified by the pinned UCD (17.0.0), the same data as
// \p{ID_Start} and General_Category: U+0558 is unassigned in Unicode 17, so it
// is not an identifier character (nor a group name), while U+00E9 is.
// expect: normal: undefined
// print: SyntaxError
// print: SyntaxError
// print: SyntaxError
// print: SyntaxError
// print: 2
// print: false true
function t(s) { try { print(String(eval(s))); } catch (e) { print(e.name); } }
t("var \u0558 = 1");
t("var a\u0558 = 1");
t("/(?<\u0558>x)/u");
t("class C { #\u0558 = 1 }");
t("var \u00e9 = 2; \u00e9");
print(/\p{ID_Start}/u.test("\u0558") + " " + /\p{Cn}/u.test("\u0558"));
