// String.prototype.replaceAll (§22.1.3.20) steps 11–12: every position of
// the search string, each advanceBy = max(1, searchLength) after the last,
// the empty search string included (length + 1 positions).
// expect: normal: undefined
// print: _a_b_c_ x-x-x **a
print('abc'.replaceAll('', '_') + " " + 'xaaxaax'.replaceAll('aa', '-') + " " + 'aaaaa'.replaceAll('aa', '*'));
