// UTC ( t ) (§21.4.1.26) step 4.d: a local time skipped at a positive time
// zone transition is interpreted with the offset before the transition (the
// last integral Number below t that has instants, tBefore). The time zone of
// --date-test-host has offset 0 before the epoch and +5 ms from it, so the
// local times 0-4 ms after the epoch are skipped.
// needs: --date-test-host
// Not run: no option of ecma-run gives Date.parse heuristics that answer 1 or a
// time zone with a transition at the epoch. Its host has only the UTC time zone
// and Date.parse by its reference parser (Engine/Host/Core.lean, `choice`).
// args: --date-test-host
// expect: normal: undefined
// print: -1 0 3 4 0 2
// print: 8 7 1970-01-01T00:00:00.003Z
var ms = [[1969, 11, 31, 23, 59, 59, 999], [1970, 0, 1, 0, 0, 0, 0], [1970, 0, 1, 0, 0, 0, 3],
  [1970, 0, 1, 0, 0, 0, 4], [1970, 0, 1, 0, 0, 0, 5], [1970, 0, 1, 0, 0, 0, 7]];
print(ms.map(function (a) { return new Date(a[0], a[1], a[2], a[3], a[4], a[5], a[6]).getTime(); }).join(" "));
var d = new Date(1970, 0, 1, 0, 0, 0, 3);
print(d.getMilliseconds() + " " + new Date(2).getMilliseconds() + " " + d.toISOString());
