// S2 end to end: recursion through a strict function declaration.
// expect: normal: 55
"use strict"; function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); } fib(10)
