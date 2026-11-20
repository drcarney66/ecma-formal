// expect: normal: "10,30,50|2,3|3,4,5|1,1,2,2|15|true,false,3|1+2|a,b,c|1:x,2:y|u,v,w"
// Iterator helpers (§27.1.3.3), Iterator.from, Iterator.concat and Iterator.zip (§27.1.3.2).
var parts = [];
parts.push([1, 2, 3, 4, 5].values().filter(function (x) { return x % 2; })
  .map(function (x) { return x * 10; }).toArray().join(","));
parts.push([1, 2, 3, 4].values().drop(1).take(2).toArray().join(","));
parts.push([1, 2, 3, 4, 5].values().drop(2).toArray().join(","));
parts.push([1, 2].values().flatMap(function (x) { return [x, x]; }).toArray().join(","));
parts.push([1, 2, 3, 4, 5].values().reduce(function (a, b) { return a + b; }));
parts.push([[1, 2].values().some(function (x) { return x > 1; }),
  [1, 2].values().every(function (x) { return x > 1; }),
  [1, 2, 3].values().find(function (x) { return x > 2; })].join(","));
var seen = [];
[1, 2].values().forEach(function (x) { seen.push(x); });
parts.push(seen.join("+"));
var n = 0;
var plain = { next: function () { n++; return n <= 3 ? { value: "abc"[n - 1], done: false } : { done: true }; } };
parts.push(Iterator.from(plain).toArray().join(","));
parts.push(Iterator.zip([[1, 2], ["x", "y", "z"]]).map(function (p) { return p.join(":"); }).toArray().join(","));
parts.push(Iterator.concat(["u"], ["v", "w"]).toArray().join(","));
parts.join("|")
