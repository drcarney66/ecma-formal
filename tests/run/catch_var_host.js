// Without §B.3.4 (not a web browser host) a var in a Catch Block that binds
// the CatchParameter's name is the Catch Early Error.
// expect: throw: SyntaxError
try { throw 1; } catch (e) { var e = 2; }
