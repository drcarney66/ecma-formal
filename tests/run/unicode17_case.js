// Unicode 17.0.0 case data (refactor R14, findings F12–F14): U+A7CE's lowercase
// mapping is new in 17.0, U+0295 is not Cased (so a following capital sigma is
// not final), and scf folds U+A7CE to U+A7CF.
// expect: normal: "true,true,true,true"
[
  '꟎'.toLowerCase() === '꟏',
  '꟏'.toUpperCase() === '꟎',
  'ʕΣ'.toLowerCase() === 'ʕσ',
  /꟎/ui.test('꟏'),
].join(',')
