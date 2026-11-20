// The with statement (§14.11): names resolve in the object first, assignments
// go to its properties, @@unscopables hides names, and the scope ends after.
// expect: normal: "1,5,outer,undefined,2"
var v = "outer", a = 0, o = { a: 1, v: 2 };
var r = [];
with (o) { r.push(a); v = 5; }
r.push(o.v, v);
o[Symbol.unscopables] = { a: true };
with (o) { r.push(typeof b); a = 2; }
r.push(a);
r.join()
