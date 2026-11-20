// expect: normal: "true,true,false"
// MaybeSimpleCaseFolding under v and i: a new empty CharSet, filled with the folded string elements of a
// class.
[/[\q{ab}]/vi.test("AB"), /^[\q{ab|cd}]$/vi.test("cD"), /[\q{ab}]/vi.test("AC")].join()
