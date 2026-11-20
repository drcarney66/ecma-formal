// args: --web-browser
// expect: normal: "0,1,2|a,b|f|3,4,x|7,8,p,q|9|d,e|u|c,2|s"
// Generator bodies run on the frame machine (DESIGN §7): a `yield` inside a
// loop, a try/finally, a destructuring default, an optional chain's argument,
// a super call's arguments, an import-free class body and `yield *` suspends
// the generator's context, and GeneratorResume continues its frames.
function* loop() { for (let i = 0; i < 3; i++) yield i; }
var out = [[...loop()].join()];
function* delegate() { yield* ["a", "b"]; }
out.push([...delegate()].join());
var fin = "";
function* withFinally() { try { yield 1; } finally { fin = "f"; } }
var g = withFinally(); g.next(); g.return(0);
out.push(fin);
function* pattern() { var [a = yield 3, b = yield 4] = []; yield a + "," + b + "," + (yield "x"); }
g = pattern();
var seen = [g.next().value, g.next(1).value, g.next(2).value];
out.push(seen.join());
function* optional() { var o = { f(x, y) { return x + "," + y; } }; return o?.f(yield 7, yield 8); }
g = optional(); var y7 = g.next().value, y8 = g.next("p").value;
out.push(y7 + "," + y8 + "," + g.next("q").value);
class Base { constructor(v) { this.v = v; } }
function* makeDerived() {
  class D extends Base { constructor() { super(9); } }
  return new D().v;
}
out.push(makeDerived().next().value);
function* rest() { var r; ({ a: r, ...r[yield "d"] } = { a: {}, b: 1 }); yield "e"; }
out.push([...rest()].join());
function* forInInit() { for (var k = yield "u" in {}) ; }
out.push([...forInInit()].join());
function* spread() { var c = yield "c"; return [c, 2]; }
g = spread(); var first = g.next().value;
out.push(first + "," + g.next(undefined).value[1]);
function* cls() { yield class { static s = "s"; }.s; }
out.push(cls().next().value);
out.join("|")
