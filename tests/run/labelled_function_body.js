// §14.13.2 IsLabelledFunction: `the |LabelledItem| of _stmt_` reads a Statement :
// LabelledStatement node through its unit production; a labelled function as a body is a
// Syntax Error (§14.6.1, §14.7.1.1), a labelled statement that is not one is not.
// expect: normal: undefined
// print: SyntaxError
// print: ok
// print: SyntaxError
// print: SyntaxError
function t(s) { try { eval(s); return "ok"; } catch (e) { return e.constructor.name; } }
print(t("if (1) l: function f() {}"));
print(t("while (0) l: m: x;"));
print(t("while (0) l: function f() {}"));
print(t("if (0) ; else a: b: function g() {}"));
