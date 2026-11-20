// expect: normal: "SyntaxError,1,SyntaxError"
// EvalDeclarationInstantiation step 7 is the formalization's (refactor R10,
// amendment A6): AllPrivateIdentifiersValid of the eval code with the Private
// Names in scope, after PerformEval has made the eval's environments (for a
// direct eval §15.1.1 waives the early error). An indirect eval's code is a
// Script whose own early error rejects `this.#x`.
class C {
  #x = 1;
  bad() { return eval('this.#y'); }
  good() { return eval('this.#x'); }
  indirect() { return (0, eval)('this.#x'); }
}
var c = new C();
var r = [];
try { c.bad(); } catch (e) { r.push(e.constructor.name); }
r.push(c.good());
try { c.indirect(); } catch (e) { r.push(e.constructor.name); }
r.join(',')
