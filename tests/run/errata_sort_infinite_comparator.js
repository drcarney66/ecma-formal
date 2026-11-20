// expect: normal: "1,2,3|3,2,1"
// A comparator that returns ±Infinity (Erratum SortInfiniteComparator): under
// the test262 reading the order is the host's, and the test host's goes by the
// result's sign.
var r = [];
r.push([3, 1, 2].sort(function (a, b) { return a < b ? -Infinity : a > b ? Infinity : 0; }).join());
r.push([1, 3, 2].sort(function (a, b) { return a < b ? Infinity : a > b ? -Infinity : 0; }).join());
r.join("|");
