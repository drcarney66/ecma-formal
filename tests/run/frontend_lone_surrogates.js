// Run-time source text may contain lone surrogates (§11.1.6 step 1): in
// string literals, comments, templates and patterns they are SourceCharacters;
// anywhere else a SyntaxError.
// expect: normal: undefined
// print: 1 d800
// print: 1
// print: true
// print: true false
// print: dc00 dc00
// print: 4
// print: dbff
// print: d800
// print: SyntaxError
// print: true
// print: true true
// print: true
function t(f) { try { print(f()); } catch (e) { print(e.name); } }
t(() => eval("'\uD800'").length + " " + eval("'\uD800'").charCodeAt(0).toString(16));
t(() => eval("/*\uD800*/1"));
t(() => new RegExp("\uD800").test("\uD800"));
t(() => new RegExp("[\uD800-\uDBFF]").test("\uDA00") + " " + new RegExp("[\uD800-\uDBFF]").test("a"));
t(() => eval("`\uDC00`").charCodeAt(0).toString(16) + " " + eval("String.raw`\uDC00`").charCodeAt(0).toString(16));
t(() => new Function("return '𐀁x\uDFFF'")().length);
t(() => eval("(function(){ '\uDBFF' })").toString().charCodeAt(13).toString(16));
t(() => eval("/\uD800/").source.charCodeAt(0).toString(16));
t(() => eval("var \uD800 = 1"));
t(() => new RegExp("[\uD800-\\uDBFF]").test("\uDA00"));
t(() => new RegExp("[\uD800-\uE000]").test("\uDA00") + " " + new RegExp("[\uD800-\uE000]", "u").test("\uDA00"));
t(() => new RegExp("\\\uD800").test("\uD800"));
