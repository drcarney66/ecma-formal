// js-run's Math host (audit F207/F330): Math.expm1 and Math.log1p of large
// finite arguments whose results are finite give finite values close to the
// ideal (Kahan's formulas, with the quotient formed before the product so it
// cannot overflow).
// expect: normal: undefined
// print: true,true,true,true,true
function close(x, ideal) { return isFinite(x) && Math.abs(x - ideal) <= Math.abs(ideal) * 1e-12; }
print([
  close(Math.expm1(709), 8.218407461554972e+307),
  Math.expm1(709) === Math.exp(709),
  close(Math.log1p(1e306), 704.591038456178),
  close(Math.log1p(2.6e305), 703.2439648082113),
  close(Math.log1p(Number.MAX_VALUE), 709.782712893384)
].join());
