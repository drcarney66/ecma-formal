// An |IdentifierName| spelling `if` with an escape is the String value of a
// terminal of |ReservedWord| (Erratum StringValueReservedWord, test262's reading).
// expect: throw: SyntaxError
var \u0069f;
