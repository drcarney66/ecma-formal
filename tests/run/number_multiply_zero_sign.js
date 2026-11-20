// expect: normal: undefined
// print: -Infinity,-Infinity,Infinity,-Infinity,Infinity,Infinity,-Infinity
// Number::multiply step 6 gives 𝔽(0) = +0 for +0 × -5; the clause's
// description (IEEE 754-2019) and every engine give -0 (Erratum
// NumberMultiplyZeroSign, read by default as proposed: no test262 assertion
// covers the case). A product that underflows keeps
// its sign by 𝔽 itself.
print(String([1 / (0 * -5), 1 / (-5 * 0), 1 / (0 * 5), 1 / (-0 * 5), 1 / (-0 * -5), 1 / (0 * 0),
  1 / (1e-300 * -1e-300)]));
