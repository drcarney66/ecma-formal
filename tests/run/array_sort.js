// Array.prototype.sort and toSorted, %TypedArray%.prototype.sort (§23.1.3.30, §23.2.3.29): the
// default order, a stable comparator sort, an inconsistent comparator's permutation.
// expect: normal: "1,2,3|a1,a2,b1,b2|3:1,2,3|1,2,3/3,1,2|1,2,3"
var r = [];
r.push([3, 1, 2].sort().join());
var ps = [["b", 1], ["a", 1], ["b", 2], ["a", 2]].sort(function (p, q) { return p[0] < q[0] ? -1 : p[0] > q[0] ? 1 : 0; });
r.push(ps.map(function (p) { return p[0] + p[1]; }).join());
var x = [2, 3, 1].sort(function () { return 1; });
r.push(x.length + ":" + x.slice().sort().join());
var o = [3, 1, 2];
r.push(o.toSorted().join() + "/" + o.join());
r.push(new Int8Array([3, 1, 2]).sort().join());
r.join("|");
