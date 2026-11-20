// A FunctionDeclaration's Evaluation is empty (§15.2.6), so UpdateEmpty keeps
// the previous statement's value.
// expect: normal: 1
1; function f() {}
