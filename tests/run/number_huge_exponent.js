// expect: normal: true
// StringToNumber on an exact decimal (RoundDecimalMV): an exponent far
// outside the range of Number gives +/-Infinity or 0 without building 10^e.
Number("1e999999999") === Infinity &&
  Number("-1e999999999") === -Infinity &&
  Number("1e-999999999") === 0 &&
  1 / Number("-1e-999999999") === -Infinity &&
  Number("0e999999999") === 0 &&
  Number(".5e-999999999") === 0 &&
  Number("5.e999999999") === Infinity
