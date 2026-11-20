// GlobalDeclarationInstantiation step 8.a.iv.2: NaN is a non-configurable,
// non-writable property of the global object, so CanDeclareGlobalFunction is false.
// expect: throw: TypeError
function NaN() {}
