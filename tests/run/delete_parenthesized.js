// expect: normal: "SyntaxError,SyntaxError,ok,ok,SyntaxError,ok"
// The delete early errors (§13.5.1.1) test a parenthesized operand as the phrase it derives,
// through every nesting: an identifier in strict code and a private member are errors.
var r = [];
function t(src) { try { (0, eval)(src); r.push("ok"); } catch (e) { r.push(e.constructor.name); } }
t('"use strict"; delete (x);');
t('"use strict"; delete ((x));');
t('"use strict"; var o = { p: 1 }; delete (o.p);');
t('delete (x);');
t('class C { #m; f() { delete ((this.#m)); } }');
t('"use strict"; var x, y; delete (x, y);');
r.join(',')
