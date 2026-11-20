// GlobalDeclarationInstantiation step 8.a.iv.2, for a generator declaration
// after a var declaration.
// expect: throw: TypeError
var x;
function* undefined() {}
