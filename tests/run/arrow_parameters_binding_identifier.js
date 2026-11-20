// ArrowParameters : BindingIdentifier and AsyncArrowBindingIdentifier have their
// own IteratorBindingInitialization (§8.6.3) and InstantiateAsyncArrowFunctionExpression
// arm (§15.9.4); the parenthesized forms go through ArrowFormalParameters.
// expect: normal: undefined
// print: 1,,2,1,1,1,0
// print: x => x|(x) => x|async x => x|async (x) => x
// print: f,g,,
// print: 7,8
var f = x => x, g = (x) => x, h = async x => x, k = async (x) => x, d = (x = 1) => x;
print([f(1), f(), g(2), f.length, g.length, h.length, d.length].join());
print([f, g, h, k].map(String).join("|"));
print([f.name, g.name, (x => x).name, (async y => y).name].join());
var log = [];
h(7).then(v => log.push(v)).then(() => k(8)).then(v => { log.push(v); print(log.join()); });
void 0;
