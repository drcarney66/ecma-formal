// IsLabelledFunction takes "the |LabelledItem| of" a |Statement| node through
// its unit chain (Erratum UnitChainChild, test262's reading): the labelled
// function in an if body is the Early Error of sec-if-statement-static-semantics-early-errors.
// args: --web-browser
// expect: throw: SyntaxError
if (1) l: function f() {}
