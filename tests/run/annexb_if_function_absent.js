// Without §B.3.3 (a host that supports only §B.3.5) an IfStatement's clause
// is no FunctionDeclaration.
// args: --annex-b sec-initializers-in-forin-statement-heads
// expect: throw: SyntaxError
if (true) function f() {}
typeof f
