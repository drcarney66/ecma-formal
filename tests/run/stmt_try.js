// try/catch/finally: a normal Finally keeps the Catch's completion value.
// expect: normal: 5
try { throw 1 } catch (e) { 5 } finally { 6 }
