// §B.3.1 on a web browser host (refactor R25): the labelled function
// declaration is evaluated, and GlobalDeclarationInstantiation binds `f`.
// args: --web-browser
// expect: normal: 7
l: function f() { return 7; }
f()
