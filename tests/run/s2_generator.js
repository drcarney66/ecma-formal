// Generator and async function objects (§15.5, §15.8, §27.8): instantiation,
// generator bodies without yield (next, return, throw), GetGeneratorKind in
// return, and String Iterators (§22.1.5) through for-of, spread and destructuring.
// expect: normal: "true | true | [object Generator] | 42 | true |  | true | caught7 | 5 | true | true | thrown3 | [1][2][1] | [object String Iterator] | x | y | true | 3 | hi | function | AsyncFunction | true | true | GeneratorFunction | 3"
var r = [];
function* g(a) { return a + 1; }
var it = g(41);
r.push(Object.getPrototypeOf(it) === g.prototype);
r.push(Object.getPrototypeOf(g.prototype) === Object.getPrototypeOf(function*(){}).prototype);
r.push(Object.prototype.toString.call(it));
var x = it.next(); r.push(x.value, x.done);
x = it.next(); r.push(x.value, x.done);
function* t() { throw 7; }
try { t().next(); } catch (e) { r.push("caught" + e); }
var i2 = g(1); x = i2.return(5); r.push(x.value, x.done, i2.next().done);
try { g(1).throw(3); } catch (e) { r.push("thrown" + e); }
var s = ""; for (var c of "a😀b") s += "[" + c.length + "]"; r.push(s);
var si = "xy"[Symbol.iterator](); r.push(Object.prototype.toString.call(si), si.next().value, si.next().value, si.next().done);
r.push([..."abc"].length);
var [x1, y1] = "hi"; r.push(x1 + y1);
r.push(typeof async function(){}, Object.getPrototypeOf(async function(){})[Symbol.toStringTag]);
try { g.prototype.next.call({}); } catch (e) { r.push(e instanceof TypeError); }
r.push(Object.getPrototypeOf(g) === Object.getPrototypeOf(function*(){}), Object.getPrototypeOf(function*(){}).constructor.name);
var o = { *m() { return 3; } }; r.push(o.m().next().value);
r.join(" | ");
