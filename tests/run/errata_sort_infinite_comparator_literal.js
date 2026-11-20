// expect: stop: sortError sec-sortindexedproperties#0 4..ccxlii.2.c
// args: --erratum SortInfiniteComparator=literal
// A comparator that returns ±Infinity (Erratum SortInfiniteComparator): the
// literal reading takes ℝ of the result, which ±∞ has none of, and stops.
// The site is a step of sort.emu's reading of step 4, which stops= cannot name.
var r = [];
r.push([3, 1, 2].sort(function (a, b) { return a < b ? -Infinity : a > b ? Infinity : 0; }).join());
r.join("|");
