// for-in (§14.7.5): own keys (array indices ascending, then strings in creation
// order), then inherited keys not shadowed; non-enumerable and symbol keys are
// skipped; a key deleted before it is reached is skipped; let heads get a new
// binding per iteration; null and undefined run no iteration.
// expect: normal: "1,3,b,a,p|q,r|x|0,1,2|2"
var proto = { p: 1, a: 9 };
var o = Object.create(proto);
o.b = 1; o[3] = 1; o.a = 1; o[1] = 1;
Object.defineProperty(o, "h", { value: 1, enumerable: false });
o[Symbol.iterator] = 1;
var r = [];
for (var k in o) r.push(k);
var s = [], d = { q: 1, z: 1, r: 1 };
for (var k2 in d) { s.push(k2); delete d.z; }
var t = [];
for (var k3 in null) t.push(k3);
for (k3 in undefined) t.push(k3);
t.push("x");
var fs = [];
for (let i in [7, 8, 9]) fs.push(function () { return i; });
var n = 0;
for (var j in { a: 1, b: 2, c: 3 }) { if (j === "b") break; n++; }
for (var j2 in { a: 1, b: 2 }) { if (j2 === "a") continue; n++; }
r.join() + "|" + s.join() + "|" + t.join() + "|" + fs.map(function (f) { return f(); }).join() + "|" + n
