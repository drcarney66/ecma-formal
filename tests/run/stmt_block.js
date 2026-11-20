// A Block's lexical declarations are instantiated by
// BlockDeclarationInstantiation; the declarations themselves are empty, and
// an `if` whose branch is empty is undefined (UpdateEmpty).
// expect: normal: undefined
{ let x = 1; const y = 2; 3; ; }
if (0) 1; else { let z; }
