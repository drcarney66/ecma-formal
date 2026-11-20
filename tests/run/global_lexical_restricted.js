// GlobalDeclarationInstantiation step 3.d: NaN is a non-configurable
// property of the global object, so it cannot be shadowed lexically.
// expect: throw: SyntaxError
let NaN;
