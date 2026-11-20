// Without §B.3.5 (a host that supports only §B.3.3) a for-in head's var
// ForBinding has no Initializer.
// args: --annex-b sec-functiondeclarations-in-ifstatement-statement-clauses
// expect: throw: SyntaxError
for (var i = 0 in {}) ;
i
