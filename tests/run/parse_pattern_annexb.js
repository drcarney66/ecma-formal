// args: --web-browser
// expect: normal: "true,true"
// §B.1.2's ParsePattern on a web-browser host (refactor R10, amendment A7):
// without a GroupName the Pattern[~NamedCaptureGroups] parse stands, so \k<a>
// is the identity escape k followed by "<a>".
// Strict, so GlobalDeclarationInstantiation's B.3.2.2 step does not apply.
"use strict";
var r = [];
r.push(/\k<a>/.test('k<a>'));
r.push(new RegExp('\\k<a>').test('k<a>'));
r.join(',')
