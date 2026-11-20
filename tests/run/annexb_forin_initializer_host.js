// §B.3.5 on a host that otherwise supports only it: a var ForBinding of a
// for-in head may have an Initializer, which is evaluated before the object.
// args: --annex-b sec-initializers-in-forin-statement-heads
// expect: normal: 0
for (var i = 0 in {}) ;
i
