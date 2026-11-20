// test262's $262.evalScript (INTERPRETING.md): ParseScript in the current Realm (§16.1.5), then
// ScriptEvaluation (§16.1.6), its completion returned. A parse or early error throws the first error of
// ParseScript's List, GlobalDeclarationInstantiation its own; a non-String throws a TypeError. A created
// realm's evalScript evaluates in that realm.
// expect: normal: "function,evalScript,1 ; 2,1,,number,,,3 ; SyntaxError,true,SyntaxError,7,TypeError ; true,5,undefined,true"
var f = $262.evalScript;
var r1 = [typeof f, f.name, f.length].join();
var r2 = [f("var x = 1; x + 1"), x, f("let y = 2;"), typeof y, f(""), f("function g() { return 3; }"), g()].join();
var e = [];
try { f("var"); } catch (x1) { e.push(x1.constructor.name, x1 instanceof SyntaxError); }
try { f("let y;"); } catch (x2) { e.push(x2.constructor.name); }
try { f("throw 7"); } catch (x3) { e.push(x3); }
try { f(1); } catch (x4) { e.push(x4.constructor.name); }
var o = $262.createRealm();
var r4 = [o.evalScript("var z = 5; this") === o.global, o.global.z, typeof z, o.evalScript("[]") instanceof o.global.Array].join();
[r1, r2, e.join(), r4].join(" ; ")
