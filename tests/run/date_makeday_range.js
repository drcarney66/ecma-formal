// MakeDay (§21.4.1.28) step 8 asks for a finite time value, that is a finite
// integral Number (§21.4.1.1): the first day of a month beyond 2^53 ms still
// has one, and only TimeClip (§21.4.1.31) bounds the result to ±8.64e15 ms.
// When no Number lies within that first day (year 10^20), MakeDay is NaN.
// expect: normal: "8540918294400000|-8639332905600000|472694400000|NaN|NaN"
[
  Date.UTC(300000, 0, -10000000),
  Date.UTC(-300000, 0, 10300000),
  Date.UTC(10000000, 0, -3651700000),
  Date.UTC(1e20, 0, 1),
  Date.UTC(300000, 0, 1)
].join("|")
