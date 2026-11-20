// expect: throw: SyntaxError
// §14.13.1 / §B.3.1 (refactor R25, F64): LabelledItem : FunctionDeclaration is
// a Syntax Error unless the code is non-strict and the host is a web browser or
// otherwise supports §B.3.1. js-run's default host does not.
l: function f() {}
