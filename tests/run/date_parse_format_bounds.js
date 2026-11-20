// Date.parse (§21.4.3.2) and the Date Time String Format (§21.4.1.32): the
// time forms are THH:mm, THH:mm:ss and THH:mm:ss.sss, so "THH:mm.sss" does not
// conform and goes to the host's implementation-specific heuristics; a string
// of the format with an out-of-bounds element value is NaN, whatever the
// host's heuristics. The --date-test-host heuristics recognize every String
// they get as 1 (`dateTestHost`), so a 1 below is a String that reached them.
// needs: --date-test-host
// Not run: no option of ecma-run gives Date.parse heuristics that answer 1 or a
// time zone with a transition at the epoch. Its host has only the UTC time zone
// and Date.parse by its reference parser (Engine/Host/Core.lean, `choice`).
// args: --date-test-host
// expect: normal: undefined
// print: 1 946684800123 946684800000 1
// print: NaN NaN NaN NaN 946771200000 NaN NaN
// print: NaN NaN NaN 946684800000
print(Date.parse("2000-01-01T00:00.123Z") + " " + Date.parse("2000-01-01T00:00:00.123Z") + " " +
  Date.parse("2000-01-01T00:00Z") + " " + Date.parse("not a date"));
print(Date.parse("2000-00-01") + " " + Date.parse("2000-13-01") + " " + Date.parse("2000-01-32") + " " +
  Date.parse("-000000-01-01T00:00:00Z") + " " + Date.parse("2000-01-01T24:00:00Z") + " " +
  Date.parse("2000-01-01T24:01Z") + " " + Date.parse("2000-01-01T00:00+24:00"));
print(Date.parse("2000-00") + " " + Date.parse("2000-01-00") + " " + Date.parse("2000-01-01T00:60Z") + " " +
  Date.parse("2000-01-01"));
