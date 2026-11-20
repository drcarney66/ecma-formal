// A throw completion ends the script; the catch-less try passes it on.
// expect: throw: 8
try { 1 } finally { 2 }
throw 8
