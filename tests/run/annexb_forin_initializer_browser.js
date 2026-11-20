// §B.3.5 on a web-browser host: a var ForBinding of a for-in head may have an
// Initializer, which is evaluated before the object.
// args: --web-browser
// expect: normal: 0
for (var a = 0 in {}) ;
a
