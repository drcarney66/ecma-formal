// Function.prototype.bind (§20.2.3.2) and bound function exotic objects (§10.4.1):
// bound this and arguments, "length" and "name", and new with a bound constructor.
// expect: normal: "7,1,2,1,bound f,true,3"
"use strict";
function f(a, b) { return [this, a, b]; }
var g = f.bind(7, 1);
var r = g.call(9, 2);
function P(x) { this.x = x; }
var Q = P.bind(null, 3);
var q = new Q();
[r[0], r[1], r[2], g.length, g.name, q instanceof P, q.x].join()
