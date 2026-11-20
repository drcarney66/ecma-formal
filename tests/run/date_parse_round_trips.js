// Date.parse (§21.4.3.2 ¶2) reads back the Strings toString, toUTCString and
// toISOString give: of a time value whose milliseconds are 0, all three (and the
// Date constructor toString's), with years before 0 and after 9999 and both ends
// of the range; of any time value, toISOString's. A String that does not read back
// shows itself in place of its "=". The default host only supports UTC.
// expect: normal: "====================================|====|NaN|NaN"
var whole = [0, -1000, 951782400000, 1456753507000, -62167219200000, -62198755200000, 253402300800000,
  8.64e15, -8.64e15];
var ms = [1456753507123, -1, 8.64e15 - 1, -8.64e15 + 1];
function same(t, s) { return Date.parse(s) === t ? "=" : s; }
[
  whole.map(function (t) {
    var d = new Date(t);
    return same(t, d.toString()) + same(t, d.toUTCString()) + same(t, d.toISOString()) +
      (new Date(d.toString()).getTime() === t ? "=" : "new Date(" + d.toString() + ")");
  }).join(""),
  ms.map(function (t) { return same(t, new Date(t).toISOString()); }).join(""),
  Date.parse(new Date(NaN).toString()),
  Date.parse(new Date(8.64e15).toISOString().replace("13T", "14T"))
].join("|")
