// GlobalDeclarationInstantiation checks lexical names (step 3) before functions
// (step 8): the SyntaxError for undefined wins over the TypeError for NaN.
// expect: throw: SyntaxError
function NaN() {}
let undefined;
