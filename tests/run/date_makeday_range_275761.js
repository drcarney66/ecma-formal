// expect: normal: undefined
// print: 8639987299200000 8640000000000000 NaN
// MakeDay step 8's "finite time value" is read as any finite integral Number
// (§21.4.1.1's definition), not one within ±8.64e15: 1 January 275761 is past
// the range, 256 days before it is not. TimeClip still bounds the result.
print(Date.UTC(275761, 0, -256) + " " + Date.UTC(275760, 8, 13) + " " + Date.UTC(275760, 8, 13, 0, 0, 0, 1));
