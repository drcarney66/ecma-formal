// Date.prototype.toLocaleString / toLocaleDateString / toLocaleTimeString (§21.4.4.38–40) on a
// host without ECMA-402 whose locale has no rules of its own: the forms of toString, toDateString
// and toTimeString (UTC); the parameters are never read; a non-Date *this* throws a TypeError.
// expect: normal: "Mon Feb 29 2016 13:45:07 GMT+0000|Mon Feb 29 2016|13:45:07 GMT+0000|Invalid Date,Invalid Date,Invalid Date|Mon Feb 29 2016 13:45:07 GMT+0000|TypeError,TypeError,TypeError,TypeError|0,0,0"
var d = new Date(Date.UTC(2016, 1, 29, 13, 45, 7, 123));
var bad = new Date(NaN);
var options = { get timeZone() { throw new Error("read"); } };
function name(thunk) { try { thunk(); return "none"; } catch (err) { return err.name; } }
[
  d.toLocaleString(),
  d.toLocaleDateString(),
  d.toLocaleTimeString(),
  [bad.toLocaleString(), bad.toLocaleDateString(), bad.toLocaleTimeString()].join(),
  d.toLocaleString("de-DE", options),
  [name(function () { Date.prototype.toLocaleString.call({}); }),
    name(function () { Date.prototype.toLocaleDateString.call(0); }),
    name(function () { Date.prototype.toLocaleTimeString.call(Date.prototype); }),
    name(function () { Date.prototype.toLocaleString.call(undefined); })].join(),
  [Date.prototype.toLocaleString.length, Date.prototype.toLocaleDateString.length,
    Date.prototype.toLocaleTimeString.length].join()
].join("|")
