// GlobalDeclarationInstantiation step 8.a.iv.2, for a labelled function
// declaration (TopLevelVarScopedDeclarations looks through labels).
// A labelled function declaration is §B.3.1's, so this runs on a web browser host.
// args: --web-browser
// expect: throw: TypeError
l: function Infinity() {}
