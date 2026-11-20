// UTC ( t ) step 4.a with a large finite local time t: MakeDay (in
// GetUTCEpochNanoseconds step 1) finds no time value on the month's first
// day and returns NaN, so the Assert of GetUTCEpochNanoseconds step 4 fails.
// First, MakeDay step 8's "finite time value": any finite integral Number, or
// one in the range a time value supports (8.64e15)? 1 January 275761 is
// outside the range, but 256 days before it is inside.
if (typeof print === "undefined") globalThis.print = console.log;
print(Date.UTC(275761, 0, -256));            // range reading: NaN; any-integral reading: 8639987299200000
print(Date.UTC(275760, 8, 13));              // the last time value, either reading
print(new Date(0).setUTCHours(1e21));        // the UTC setter: no UTC(t), NaN
print(new Date(0).setHours(1e21));           // local: UTC(t) with t = 3.6e27
print(new Date(2000, 0, 1, 1e21).getTime()); // the constructor: UTC(t)
