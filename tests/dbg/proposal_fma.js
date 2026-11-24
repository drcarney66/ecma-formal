// (1 + 2^-52) * (1 - 2^-52) = 1 - 2^-104 in R.
// Naive a * b + (-1) rounds a * b to 1 first and loses the -2^-104 residual!
const a = 1 + 2 ** -52;
const b = 1 - 2 ** -52;
const naive = a * b + (-1);
const exact = Math.fusedMultiplyAdd(a, b, -1);
print("naive=" + naive + ", fma=" + exact + ", exactMatch=" + (exact === -(2 ** -104)));
