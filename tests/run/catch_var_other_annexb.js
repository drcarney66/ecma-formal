// A host that otherwise supports only §B.3.1, neither a web browser nor
// supporting §B.3.4: a var in a Catch Block that binds the name of the
// CatchParameter is the Catch Early Error (§14.15.1).
// args: --annex-b sec-labelled-function-declarations
// expect: throw: SyntaxError
try { throw 1; } catch (e) { var e = 2; }
