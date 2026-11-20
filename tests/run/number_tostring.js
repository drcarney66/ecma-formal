// Number::toString picks E notation from 1e21 on.
// expect: normal: "1e+21 123456789012345680000 1.23e-18 5e-324"
1e21 + " " + 123456789012345678901 + " " + 123e-20 + " " + 5e-324
