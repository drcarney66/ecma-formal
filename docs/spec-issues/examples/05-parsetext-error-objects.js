// ParseText returns "a List of one or more SyntaxError objects". No
// algorithm reads the List's objects: PerformEval throws its own SyntaxError
// (step 11.b), from the current realm.
if (typeof print === "undefined") globalThis.print = console.log;
try { eval("var x = ;"); } catch (e) { print(e instanceof SyntaxError); }
try { Function("a", "return a +;"); } catch (e) { print(e instanceof SyntaxError); }
try { new RegExp("("); } catch (e) { print(e instanceof SyntaxError); }
