// Reflect.ownKeys over indices, Strings and Symbols created interleaved:
// indices ascending, then Strings, then Symbols, each in creation order; many
// Symbol keys.
// expect: normal: "1,2,10,b,a,c|Symbol(s1),Symbol(s0),Symbol(s2)|20|s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19"
var s0 = Symbol('s0'), s1 = Symbol('s1'), s2 = Symbol('s2');
var o = {};
o.b = 1; o[s1] = 1; o[10] = 1; o.a = 1; o[2] = 1; o[s0] = 1; o.c = 1; o[1] = 1; o[s2] = 1;
var keys = Reflect.ownKeys(o);
var strs = keys.filter(function (k) { return typeof k === 'string'; });
var syms = keys.filter(function (k) { return typeof k === 'symbol'; }).map(String);
var p = {};
var many = [];
for (var i = 0; i < 20; i++) { var s = Symbol('s' + i); many.push(s); p[s] = i; }
var pk = Object.getOwnPropertySymbols(p);
strs.join() + '|' + syms.join() + '|' + pk.length + '|' + pk.map(function (s) { return s.description; }).join()
