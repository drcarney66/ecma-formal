// A NumericLiteral property name is ToString of its value: 0x10 is "16".
// expect: normal: 2
({0x10: 2, 1.5: 3})[16]
