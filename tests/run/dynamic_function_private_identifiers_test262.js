// args: --erratum CreateDynamicFunctionPrivateIdentifiers=test262
// expect: normal: undefined
// print: body: SyntaxError
// print: params: no error
// print: generator body: SyntaxError
// Erratum CreateDynamicFunctionPrivateIdentifiers, its test262 reading
// (spec/formal/readings.emu): after step 25, AllPrivateIdentifiersValid of the
// body only, a SyntaxError where it is false, which is all test262's
// built-ins/Function/private-identifiers-not-empty.js asserts. The parameters'
// `{}.#g` is then no error (a call of that function would stop in
// ResolvePrivateIdentifier).
try { new Function("o", "return o.#f"); print("body: no error"); }
catch (e) { print("body: " + e.constructor.name); }
try { new Function("a = {}.#g", ""); print("params: no error"); }
catch (e) { print("params: " + e.constructor.name); }
var GeneratorFunction = Object.getPrototypeOf(function* () {}).constructor;
try { GeneratorFunction("o", "yield o.#h"); print("generator body: no error"); }
catch (e) { print("generator body: " + e.constructor.name); }
