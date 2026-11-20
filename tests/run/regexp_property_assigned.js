// \p{Assigned} is every code point whose General_Category is not Unassigned
// (Cn): U+0378 and U+10FFFF are Cn in UCD 17.0.0, so \p{Assigned} does not
// match them and \P{Assigned} does (§22.2.2.9 CompileToCharSet,
// LoneUnicodePropertyNameOrValue step 5; table-binary-unicode-properties).
// expect: normal: undefined
// print: false true true
// print: true true false
// print: false true
// print: false true
print(/\p{Assigned}/u.test('͸') + ' ' + /\P{Assigned}/u.test('͸') + ' ' + /\p{Cn}/u.test('͸'));
print(/\P{Assigned}/u.test('\u{10FFFF}') + ' ' + /\p{Assigned}/u.test('A') + ' ' + /\P{Assigned}/u.test('A'));
print(/[\p{Assigned}]/u.test('͸') + ' ' + /^[^\p{Assigned}]$/u.test('͸'));
print(/[\p{Assigned}&&\p{Cn}]/v.test('͸') + ' ' + /[\p{Cn}--\p{Assigned}]/v.test('͸'));
