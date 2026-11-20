// ParseJSON step 1 (§25.5.2.1): a text that is not valid ECMA-404 JSON.
// expect: throw: SyntaxError
JSON.parse("[1, 2,]")
