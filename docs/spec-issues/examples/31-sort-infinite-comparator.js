// SortIndexedProperties: a <C b means ℝ(comparator(a, b)) < 0, and ℝ(±∞) is not defined, so a comparator
// that returns ±∞ is neither consistent nor inconsistent by the definition.
if (typeof print === "undefined") globalThis.print = console.log;
print([3, 1, 2].sort((a, b) => a < b ? -Infinity : a > b ? Infinity : 0).join());
print([5, 3, 4, 1, 2].sort((a, b) => (a - b) * Infinity).join());
print(["b", "a", "c"].sort((a, b) => a < b ? -Infinity : a > b ? Infinity : 0).join());
