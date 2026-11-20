// expect: stop: sortError sec-typeof-operator-runtime-semantics-evaluation#0 13
// args: --erratum SplitCodeUnitStrings=literal
// String.prototype.split with the empty String as separator (Erratum SplitCodeUnitStrings):
// the literal step puts code units in the Array, which are no language values, and
// typeof stops on one.
typeof "ab".split("")[1];
