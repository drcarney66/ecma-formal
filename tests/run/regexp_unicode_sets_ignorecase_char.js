// expect: normal: "true,true,true,true,false"
// MaybeSimpleCaseFolding under v and i: a class's single characters, each folded as a sequence of one.
[/[a]/vi.test("A"), /^[a-c]$/vi.test("B"), /^[\q{a|bc}]$/vi.test("A"), /^[\q{a|bc}]$/vi.test("bC"),
  /[a]/vi.test("b")].join()
