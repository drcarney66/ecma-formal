// S2 end to end: new on an ECMAScript function: OrdinaryCreateFromConstructor and instanceof.
// expect: normal: 8
"use strict"; function P(x) { this.x = x; } var p = new P(7); p.x + (p instanceof P ? 1 : 0)
