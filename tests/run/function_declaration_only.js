// A script of one FunctionDeclaration completes with empty, which
// ScriptEvaluation step 13.b turns into undefined.
// expect: normal: undefined
function f(a, b = 2) { return a + b; }
