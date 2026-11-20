// Number.prototype.toFixed, toExponential and toPrecision (§21.1.3), computed
// exactly on the value of the Number.
// expect: normal: "1.00,1000000000000000128,-2,1,1e+21|1.23e+2,0e+0,1.23456e+5,-1e-5|123.5,0.00012,1.2e+5,1.00e+21,100"
[[(1.005).toFixed(2), (1000000000000000128).toFixed(0), (-1.5).toFixed(0), (0.5).toFixed(0), (1e21).toFixed(2)].join(),
 [(123.456).toExponential(2), (0).toExponential(), (123456).toExponential(), (-0.00001).toExponential()].join(),
 [(123.456).toPrecision(4), (0.000123).toPrecision(2), (123456).toPrecision(2), (1e21).toPrecision(3), (99.99).toPrecision(3)].join()].join("|")
