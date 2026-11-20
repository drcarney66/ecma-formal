// expect: throw: SyntaxError
// §B.1.2 (refactor R25, F55): without §B.1.2 a Pattern is the main grammar's,
// and a class range with a class escape, `[\d-a]`, is an early error
// (spec.html:37533). js-run's default host does not support §B.1.2, so the
// literal is a SyntaxError.
/[\d-a]/;
