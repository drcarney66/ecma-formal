// CreateDynamicFunction (§20.2.1.1.1) steps 17-24: the parameters and the body
// are each parsed alone (steps 17 and 19, with the kind's grammar), and then the
// whole source text (step 23). A comment or bracket that only balances across
// the parameters and the body is a SyntaxError, for every kind; a line comment
// ends at the LINE FEED that steps 14-15 put after the parameters and the body.
// expect: normal: "SyntaxError|SyntaxError|SyntaxError|SyntaxError|SyntaxError|5|1|3|SyntaxError"
function name(thunk) { try { thunk(); return "none"; } catch (e) { return e.name; } }
var GeneratorFunction = Object.getPrototypeOf(function* () {}).constructor;
var AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
var AsyncGeneratorFunction = Object.getPrototypeOf(async function* () {}).constructor;
[
  name(function () { new Function("/*", "*/){"); }),
  name(function () { new Function("/", "/ ) {"); }),
  name(function () { GeneratorFunction("/*", "*/){"); }),
  name(function () { AsyncFunction("/*", "*/){"); }),
  name(function () { AsyncGeneratorFunction("/*", "*/){"); }),
  new Function("a //", "return a")(5),
  new Function("return 1 //")(),
  new Function("a /* x */", "b", "return a + b")(1, 2),
  // step 17's paramGrammar: yield is a keyword in a generator's parameters
  name(function () { GeneratorFunction("yield", ""); })
].join("|")
