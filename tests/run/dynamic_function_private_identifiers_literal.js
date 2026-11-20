// args: --erratum CreateDynamicFunctionPrivateIdentifiers=literal
// expect: normal: undefined
// print: body: no error
// print: params: no error
// print: generator body: no error
// Erratum CreateDynamicFunctionPrivateIdentifiers, the literal text: no goal of
// CreateDynamicFunction (FormalParameters, FunctionBody, FunctionExpression and
// their generator and async forms) applies AllPrivateIdentifiersValid, so each
// function is created with a null PrivateEnvironment and none is an error.
try { new Function("o", "return o.#f"); print("body: no error"); }
catch (e) { print("body: " + e.constructor.name); }
try { new Function("a = {}.#g", ""); print("params: no error"); }
catch (e) { print("params: " + e.constructor.name); }
var GeneratorFunction = Object.getPrototypeOf(function* () {}).constructor;
try { GeneratorFunction("o", "yield o.#h"); print("generator body: no error"); }
catch (e) { print("generator body: " + e.constructor.name); }
