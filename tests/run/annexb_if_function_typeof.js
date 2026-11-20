// §B.3.3 on a host that otherwise supports it and not §B.3.2: the synthetic
// Block of an if-clause FunctionDeclaration is an ordinary Block (§B.3.2's
// steps keep their own gate), so f is not bound in g's scope.
// args: --annex-b sec-functiondeclarations-in-ifstatement-statement-clauses
// expect: normal: "undefined"
function g(){ if (true) function f(){} return typeof f; }
g()
