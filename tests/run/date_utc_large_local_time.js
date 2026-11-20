// expect: stop: erratum GetUTCEpochNanosecondsNaN sec-getutcepochnanoseconds#0 4
// UTC ( t ) of a large finite local time: setHours(1e21) gives t = 3.6e24,
// GetUTCEpochNanoseconds step 1's MakeDay finds no time value on the month's
// first day (NaN), and the Assert of its step 4 fails. No test262 test
// reaches it, and the default reading is the text as written (Erratum
// GetUTCEpochNanosecondsNaN), so the run stops.
// Engines give NaN. The UTC setter does not call UTC ( t ): NaN.
print(String(new Date(0).setUTCHours(1e21)));
print(String(new Date(0).setHours(1e21)));
