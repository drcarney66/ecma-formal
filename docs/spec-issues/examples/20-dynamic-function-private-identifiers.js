if (typeof print === "undefined") globalThis.print = console.log;
// AllPrivateIdentifiersValid is checked only for a Script or Module body.
try { new Function("o", "return o.#f"); print("body: no error"); }
catch (e) { print("body: " + e.constructor.name); }
try { new Function("a = {}.#g", ""); print("params: no error"); }
catch (e) { print("params: " + e.constructor.name); }
try { eval("(function (o) { return o.#f; })"); print("eval: no error"); }
catch (e) { print("eval: " + e.constructor.name); }
