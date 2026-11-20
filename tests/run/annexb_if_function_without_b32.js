// §B.3.3 without §B.3.2: the synthetic Block of an if-clause
// FunctionDeclaration is a Block for the §B.3.2 steps, each of which keeps
// its own gate "If the host is a web browser or otherwise supports §B.3.2"
// (IfStatement.clauseEvaluation), so f is bound only in the synthetic Block.
// args: --annex-b sec-functiondeclarations-in-ifstatement-statement-clauses
// expect: normal: undefined
// print: undefined,undefined
function g(){ var before = typeof f; if (true) function f(){} return before + "," + typeof f; }
print(g());
