// §B.1.2 on a web-browser host, parsing only: the literals pass B.1.2.1's early
// errors (\k without a GroupName is an identity escape, a class range may have a
// class escape end), and ParsePattern's B.1.2.9 step reparses with
// +NamedCaptureGroups only where a GroupName occurs; with u it is §22.2's parse.
// Strict, so GlobalDeclarationInstantiation's B.3.2.2 step does not apply.
// args: --web-browser
// expect: normal: "SyntaxError,SyntaxError,SyntaxError,SyntaxError"
"use strict";
var unused = () => [/\k/, /\k<a>/, /(?<a>.)\k<a>/, /[\d-a]/, /[a-\d]/];
function name(s, f) { try { new RegExp(s, f); return "none"; } catch (e) { return e.name; } }
[name("(?<a>.)\\k<b>", ""), name("\\k", "u"), name("[\\d-a]", "u"), name("[a-\\d]", "u")].join()
