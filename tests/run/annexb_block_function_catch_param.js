// A host that supports §B.3.2 but not §B.3.4: replacing a block
// FunctionDeclaration named like a simple CatchParameter with a var would be
// the Catch Early Error (§14.15.1, whose BindingIdentifier exemption needs
// §B.3.4), so FDI 32.a.i.2, GDI 12.b.ii.2 and EDI 13.b.ii do not hoist it.
// args: --annex-b sec-block-level-function-declarations-web-legacy-compatibility-semantics
// expect: normal: undefined
// print: undefined
// print: undefined false
// print: undefined
print((function(){ try { throw 1 } catch (e) { { function e(){} } } return typeof e })());
try { throw 0 } catch (g) { { function g(){} } }
print(typeof g + " " + (Object.getOwnPropertyDescriptor(globalThis, "g") !== undefined));
print(eval("try { throw 0 } catch (h) { { function h(){} } } typeof h"));
