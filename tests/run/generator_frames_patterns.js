// expect: normal: "a,k=1,2,cd|x=6,5|q,s=1/3/4/|m,i=7,89|u,v=UV|key,heritage,s=mfB1false|1,2,3,4=aAbBcx_y_zCD|e,f,g,h,i,j,callee,q,t=123;A;2;9;13;T|1,2=1:10x 2:20y 211"
// More of the frame machine (DESIGN §7), each construct suspended by a `yield`
// inside it: object and array patterns (keyed, defaults, rest, elisions, an
// assignment pattern's targets), a class definition (a computed key, its
// heritage, a static field, a named evaluation), template literals and a
// tagged template, array and object literals, operators, calls and an
// optional chain, and a `for…of` whose binding is a pattern and whose `break`
// closes the iterator.
function run(gen, values) {
  var g = gen(), r = g.next(), seen = [];
  for (var i = 0; !r.done; i++) { seen.push(r.value); r = g.next(values[i]); }
  return seen.join() + "=" + r.value;
}
var out = [];
// object patterns
out.push(run(function* () {
  var { a = yield "a", [yield "k"]: b, ...rest } = { k: 2, c: 3, d: 4 };
  return a + "," + b + "," + Object.keys(rest).join("");
}, [1, "k"]));
out.push(run(function* () {
  var o = {}, r;
  ({ x: o.x = yield "x", ...r } = { y: 5 });
  return o.x + "," + r.y;
}, [6]));
// array patterns
out.push(run(function* () {
  var [p, , q = yield "q", ...[s = yield "s", t]] = [1, 2];
  return [p, q, s, t].join("/");
}, [3, 4]));
out.push(run(function* () {
  var o = {}, arr = [];
  [o.m = yield "m", ...arr[yield "i"]] = [undefined, 8, 9];
  return o.m + "," + arr[0].join("");
}, [7, 0]));
out.push(run(function* () {
  var [[u = yield "u"] = [], { v = yield "v" } = {}] = [];
  return u + v;
}, ["U", "V"]));
// classes
out.push(run(function* () {
  class A { [yield "key"]() { return "m"; } static f = "f"; }
  var B = class extends (yield "heritage") { static [yield "s"] = 1; };
  return new A().k() + A.f + B.name + B.s + (new B() instanceof A);
}, ["k", A0(), "s"]));
function A0() { return class { }; }
// templates
out.push(run(function* () {
  function tag(strings, ...subs) { return strings.raw.join("_") + subs.join(""); }
  return `a${yield 1}b${yield 2}c` + tag`x${yield 3}y${yield 4}z`;
}, ["A", "B", "C", "D"]));
// literals, operators, calls, chains
out.push(run(function* () {
  var o = { m(x, y) { return x * y; }, p: { q: 4 } };
  var arr = [1, yield "e", 3];
  var obj = { a: yield "f", [yield "g"]: 2 };
  var n = -(yield "h") + (yield "i") * 2;
  var c = o.m(yield "j", 3) + (yield "callee")(2) + o?.p[yield "q"];
  var t;
  t = yield "t";
  return [arr.join(""), obj.a, obj.b, n, c, t].join(";");
}, [2, "A", "b", 1, 5, 2, function (z) { return z + 1; }, "q", "T"]));
// for…of with a pattern binding, and a break that closes the iterator
var closed = 0;
var iterable = { [Symbol.iterator]() {
  var i = 0;
  return { next() { i++; return { value: [i, i * 10], done: i > 3 }; },
    return() { closed++; return {}; } };
} };
out.push(run(function* () {
  var s = "";
  for (var [i, j = yield "never"] of iterable) { s += i + ":" + j + (yield i) + " "; if (i == 2) break; }
  for (let { length } of ["ab", "c"]) s += length;
  return s + closed;
}, ["x", "y"]));
out.join("|")
