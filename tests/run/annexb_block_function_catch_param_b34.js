// With §B.3.2 and §B.3.4 (and no other Annex B section) the simple
// CatchParameter does not conflict, so the block function is hoisted
// (FDI 32.a.i, GDI 12.b.ii, EDI 13.b).
// args: --annex-b sec-block-level-function-declarations-web-legacy-compatibility-semantics --annex-b sec-variablestatements-in-catch-blocks
// expect: normal: undefined
// print: function
// print: function true
// print: function
print((function(){ try { throw 1 } catch (e) { { function e(){} } } return typeof e })());
try { throw 0 } catch (g) { { function g(){} } }
print(typeof g + " " + (Object.getOwnPropertyDescriptor(globalThis, "g") !== undefined));
print(eval("try { throw 0 } catch (h) { { function h(){} } } typeof h"));
