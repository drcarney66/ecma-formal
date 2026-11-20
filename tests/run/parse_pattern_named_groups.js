// expect: normal: "true,true,false"
// ParsePattern with its ParseText calls (refactor R10, amendment A7): with a
// GroupName the pattern is parsed with [+NamedCaptureGroups] (step 4.a of the
// main grammar; on a web browser §B.1.2 step 4.b reparses), so \k<a> is a
// backreference.
var r = [];
r.push(/(?<a>.)\k<a>/.test('xx'));
r.push(/(?<a>.)\k<a>/u.test('xx'));
r.push(/(?<a>.)\k<a>/.test('xy'));
r.join(',')
