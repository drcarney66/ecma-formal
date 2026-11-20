"use strict";
// IsInTailPosition: the call in `return (paren(n - 1))` lies in the ParenthesizedExpression that the cover
// covers, which §5.1.4 parses as a separate tree containing no FunctionBody.
if (typeof print === "undefined") globalThis.print = console.log;
function plain(n) { if (n === 0) return "done"; return plain(n - 1); }
function paren(n) { if (n === 0) return "done"; return (paren(n - 1)); }
for (var [name, fn] of [["plain", plain], ["paren", paren]]) {
  try { print(name + ": " + fn(100000)); }
  catch (e) { print(name + ": " + e.constructor.name); }
}
