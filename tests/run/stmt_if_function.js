// expect: throw: SyntaxError
// §B.3.3: `if (x) function f() {}` parses only on a host that supports §B.3.3
// (a web browser, or one that otherwise supports it): on js-run's default host
// the frontend reports the SyntaxError, and the statement is never evaluated
// (the evaluator's `AnnexB.require` would stop with assertFailed).
1; if (true) function f() {}
