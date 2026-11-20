// Array.from, find*, reduce*, sort (stable, undefined last), splice, fill,
// copyWithin and the copying methods (§23.1).
// expect: normal: "x,y|2,1|10|c-b-a|1,10,2,3,|b1,b2,a1|1,a,b,4,5/2,3|1,0,0|4,5,3,4,5|3,2,1|1,9|1,4"
var r = [];
r.push(Array.from({ length: 2, 0: "x", 1: "y" }).join());
r.push([1, 2, 3].find(function (x) { return x > 1; }) + "," + [1, 2, 3].findLastIndex(function (x) { return x < 3; }));
r.push([1, 2, 3, 4].reduce(function (a, b) { return a + b; }));
r.push(["a", "b", "c"].reduceRight(function (a, b) { return a + "-" + b; }));
r.push([3, undefined, 1, 10, 2].sort().join());
var pairs = [["b", 1], ["a", 1], ["b", 2]].sort(function (p, q) { return p[0] < q[0] ? 1 : p[0] > q[0] ? -1 : 0; });
r.push(pairs.map(function (p) { return p[0] + p[1]; }).join());
var a = [1, 2, 3, 4, 5], d = a.splice(1, 2, "a", "b");
r.push(a.join() + "/" + d.join());
r.push([1, 2, 3].fill(0, 1).join());
r.push([1, 2, 3, 4, 5].copyWithin(0, 3).join());
r.push([1, 2, 3].toReversed().join());
r.push([1, 2].with(1, 9).join());
r.push([1, 2, 3, 4].toSpliced(1, 2).join());
r.join("|")
