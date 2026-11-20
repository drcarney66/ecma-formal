// expect: normal: "1|SyntaxError"
// PropName of PropertyDefinition : CoverInitializedName (the row the overlay adds,
// syntax.emu row-propname-coverinitializedname): the row lets the object
// literal's PropertyNameList be computed; as an assignment pattern the program
// runs, as an object literal it is a SyntaxError.
var r = [];
var a;
({a = 1} = {});
r.push(a);
try { eval("({b = 1})"); } catch (e) { r.push(e.constructor.name); }
r.join("|");
