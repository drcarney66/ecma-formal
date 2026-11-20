// expect: normal: "SyntaxError,SyntaxError,3,1,SyntaxError,function,true"
// CreateDynamicFunction steps 17-24 are three ParseText calls (refactor R10,
// amendment A2, findings F6 and F43): the parameters and the body are each
// valid alone (step 21's NOTE), a generator's FormalParameters[+Yield] reject
// `yield` (step 17 with the generator's goal), and step 28 makes the function
// from the Parse Nodes of steps 17 and 19. The SyntaxErrors are the current
// realm's (Erratum ParseTextErrorObjects: ParseText allocates no error object).
function kind(f) { try { f(); return 'no error'; } catch (e) { return e.constructor.name; } }
var GeneratorFunction = Object.getPrototypeOf(function* () {}).constructor;
var AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
var r = [];
r.push(kind(() => new Function('/*', '*/){')));
r.push(kind(() => new Function('/', '/ ) {')));
r.push(new Function('a', 'b', 'return a+b')(1, 2));
r.push(GeneratorFunction('yield 1')().next().value);
r.push(kind(() => GeneratorFunction('a = yield', '')));
r.push(typeof new AsyncFunction('await 1'));
try { new Function('}'); } catch (e) { r.push(e instanceof SyntaxError); }
r.join(',')
