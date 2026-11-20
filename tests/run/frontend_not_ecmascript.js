// Proposal and TypeScript syntax that the parser accepts is not in the pinned
// grammar: a SyntaxError (a getter's rest parameter too, §15.4).
// expect: normal: undefined
// print: SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError SyntaxError
// print: ok
function t(s) { try { eval(s); return "ok"; } catch (e) { return e.name; } }
print([
  "@dec class C {}", "class C { accessor x = 1 }", "import.source('x')", "import.defer('x')",
  "class C { public x = 1 }", "class C { private m() {} }", "class C { private static m() {} }",
  "class C { readonly y = 2 }", "class C { override o() {} }", "class C { declare z; }",
  "class C { accessor a() {} }", "class C { w? = 3 }", "class C { m?() {} }",
  "({ get x(...a) {} })", "class C { get y(...r) {} }", "new Function('@dec class C {}')",
].map(t).join(" "));
print(t("class C { static async *m() {} static get [1]() {} get(){} set(){} static(){} async(){} static static(){} }"));
