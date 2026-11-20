// BigInt against Number and String: 1n == 1, 1n == "1", 1n !== 1, 1n < "x" is false, 2n > "1".
// expect: normal: true
1n == 1 && 1n == "1" && 1n !== 1 && !(1n < "x") && !(1n >= "x") && 2n > "1"
