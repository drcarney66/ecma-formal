// SwitchStatement Evaluation: blockEnv's [[DisposableResourceStack]] is an empty List at step 8,
// with an empty CaseBlock and with a lexical binding in a clause.
// expect: normal: true
var a = eval("switch (0) {}");
var b = eval("switch (0) { case 0: let x = 7; x; }");
a === undefined && b === 7;
