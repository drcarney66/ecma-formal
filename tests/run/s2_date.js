// Date objects (§21.4): the time value arithmetic, the Date constructor,
// Date.parse of the Date Time String Format and of toString / toUTCString
// output, and the String forms. The default host only supports UTC, and its
// clock starts at the epoch and moves a millisecond at each reading of the
// current time (Host.elapsed: Date() reads 1, Date.now() 2).
// expect: normal: "1456753507123|Mon Feb 29 2016 13:45:07 GMT+0000|2016-02-29T13:45:07.123Z|Mon, 29 Feb 2016 13:45:07 GMT|1,2016,1,29|1456753507000|1456753507123|1456704000000|NaN|-271821-04-20T00:00:00.000Z|Invalid Date|Thu Jan 01 1970 00:00:00 GMT+0000|29312|1899,-1|2,true|1456790400000|+275760-09-13T00:00:00.000Z|RangeError"
var d = new Date(2016, 1, 29, 13, 45, 7, 123);
var e = new Date(0);
e.setUTCFullYear(2016, 1, 30);
function name(thunk) { try { thunk(); return "none"; } catch (err) { return err.name; } }
[
  d.getTime(),
  d.toString(),
  d.toISOString(),
  d.toUTCString(),
  [d.getDay(), d.getFullYear(), d.getMonth(), d.getDate()].join(),
  Date.parse(d.toString()),
  Date.parse(d.toISOString()),
  Date.parse("2016-02-29"),
  Date.UTC(275760, 8, 13, 0, 0, 0, 1),
  new Date(-8640000000000000).toISOString(),
  String(new Date(NaN)),
  Date(),
  Date.UTC(1970, 0, 1, 80063993375, 29, 1, -288230376151711740),
  [new Date(1899, 11, 31).getFullYear(), new Date(-1, 0).getFullYear()].join(),
  [Date.now(), new Date(e) - e === 0].join(),
  e.valueOf(),
  new Date(8.64e15).toISOString(),
  name(function () { new Date(NaN).toISOString(); })
].join("|")
