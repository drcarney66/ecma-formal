// expect: normal: undefined
// print: number
// print: number
// print: undefined
// A Use Strict Directive is the exact source text "use strict" or 'use strict'
// (§11.2.1; refactor R11, finding F38): a directive with an escape or a line
// continuation has the SV "use strict" but is not one, so these eval codes are
// not strict and their var declarations are the global object's.
eval("'use\\x20strict'; var viaEscape = 1;");
print(typeof viaEscape);
eval("'use \\\nstrict'; var viaContinuation = 1;");
print(typeof viaContinuation);
eval("'use strict'; var strictVar = 1;");
print(typeof strictVar);
void 0;
