// expect: stop: sortError sec-islabelledfunction#0 2
// Erratum UnitChainChild read literally: "the |LabelledItem| of" a |Statement|
// node names a child its production does not have, and the run stops.
// args: --web-browser --literal UnitChainChild
if (1) l: function f() {}
