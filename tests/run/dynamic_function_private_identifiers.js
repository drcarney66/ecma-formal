// expect: normal: undefined
// print: body: SyntaxError
// print: params: SyntaxError
// print: generator body: SyntaxError
// CreateDynamicFunction steps 18-29: no goal it parses with applies
// AllPrivateIdentifiersValid (Erratum CreateDynamicFunctionPrivateIdentifiers).
// The default reading, the proposed one, adds after step 25
// "If AllPrivateIdentifiersValid of _body_ with argument « » is false, throw a
// SyntaxError exception" and the same of _params_ (spec/formal/readings.emu):
// engines parse the parameters and the body as one source text and throw for
// both. The test262 reading checks the body only, which is all test262's
// built-ins/Function/private-identifiers-not-empty.js asserts
// (dynamic_function_private_identifiers_test262.js); the literal text checks
// neither (dynamic_function_private_identifiers_literal.js).
try { new Function("o", "return o.#f"); print("body: no error"); }
catch (e) { print("body: " + e.constructor.name); }
try { new Function("a = {}.#g", ""); print("params: no error"); }
catch (e) { print("params: " + e.constructor.name); }
var GeneratorFunction = Object.getPrototypeOf(function* () {}).constructor;
try { GeneratorFunction("o", "yield o.#h"); print("generator body: no error"); }
catch (e) { print("generator body: " + e.constructor.name); }
