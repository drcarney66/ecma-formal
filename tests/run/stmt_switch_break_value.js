// Falling through into `break;`: UpdateEmpty(break, 5) keeps the value 5, and
// a `continue` passes through a switch to the enclosing loop.
// expect: normal: 4
switch (1) { case 1: 5; case 2: break; }
do { switch (1) { case 1: 4; continue; } 6; } while (false)
