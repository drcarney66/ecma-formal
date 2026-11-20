// Optional chains (§13.3.9): a nullish base short-circuits the whole chain,
// and a call through `?.` keeps its this value.
// expect: normal: ",,1,ok"
var o = { a: { b: 1 }, f() { return this === o ? "ok" : "bad"; } };
var n = null;
[n?.a.b.c, o.x?.y(), o?.a.b, o.f?.()].join()
