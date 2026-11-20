// DisposableStack.prototype.adopt registers a built-in closure that calls
// onDispose with this undefined and the adopted value (§27.3.3.1).
// expect: normal: "undefined:v"
var r;
var stack = new DisposableStack();
stack.adopt("v", function (value) { "use strict"; r = typeof this + ":" + value; });
stack.dispose();
r
