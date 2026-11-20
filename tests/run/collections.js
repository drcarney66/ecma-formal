// Keyed collections (§24), WeakRef and FinalizationRegistry (§26),
// Object.groupBy and Map.groupBy: insertion order, SameValueZero keys,
// iterators that see later additions, the set methods, and weak keys.
// expect: normal: "a,c,d|2|1,2,3|2|1|1,3|true,false,true|x,y|3|true|odd:1,3;even:2;1,3|true,false|TypeError"
var m = new Map([["a", 1], ["b", 2]]);
m.delete("b");
m.set("c", 3);
var keys = [];
for (var k of m.keys()) { keys.push(k); if (k === "a") m.set("d", 4); }
var s = new Set([1, 2]);
s.add(-0).add(0).delete(0);
var other = new Set([2, 3]);
var wm = new WeakMap();
var o = {};
wm.set(o, "x");
var ws = new WeakSet([o]);
var wr = new WeakRef(o);
var fr = new FinalizationRegistry(function () {});
fr.register(o, "held", o);
var g = Object.groupBy([1, 2, 3], function (x) { return x % 2 ? "odd" : "even"; });
var mg = Map.groupBy([1, 2, 3], function (x) { return x % 2; });
function name(thunk) { try { thunk(); return "none"; } catch (err) { return err.name; } }
[
  keys.join(),
  s.size,
  Array.from(s.union(other)).join(),
  Array.from(s.intersection(other)).join(),
  Array.from(s.difference(other)).join(),
  Array.from(s.symmetricDifference(other)).join(),
  [s.isSubsetOf(new Set([1, 2, 3])), s.isSupersetOf(other), s.isDisjointFrom(new Set([4]))].join(),
  [wm.get(o), wm.getOrInsert({}, "y")].join(),
  new Map([[NaN, 1]]).getOrInsertComputed(NaN, function () { return 9; }) + 2,
  wr.deref() === o && ws.has(o),
  "odd:" + g.odd.join() + ";even:" + g.even.join() + ";" + mg.get(1).join(),
  [fr.unregister(o), fr.unregister(o)].join(),
  name(function () { wm.set(1, 2); })
].join("|")
