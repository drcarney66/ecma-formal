// Number::toString step 5 at 2^-1073: s = 9 (n = -323) and s = 1 (n = -322) both have k = 1;
// the engine's digits take the one closer to 2^-1073 (9.88e-324), 1e-323, as the step's NOTE recommends.
// expect: normal: undefined
// print: 1e-323
print(2**-1073)
