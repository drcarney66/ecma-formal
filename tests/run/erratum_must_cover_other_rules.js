// The cover's must-cover rule is applied first and reports the error; the
// node's other rules, which read through the cover, are not applied (overlay clause
// formal-early-errors-cover-rules-first; decisions.md row early-errors-cover-first).
// expect: throw: SyntaxError
async (...x = []) => {};
