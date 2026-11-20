// expect: stop: sortError ph-stringvalue-any-nt-except#0 1
// Erratum StringValueReservedWord read literally: the rule takes the
// StringValue of a |ReservedWord|, which has none, and the run stops.
// args: --literal StringValueReservedWord
var \u0069f;
