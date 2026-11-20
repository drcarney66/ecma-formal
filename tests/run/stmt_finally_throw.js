// An abrupt Finally replaces the Catch's completion.
// expect: throw: 4
try { throw 1 } catch { 3 } finally { throw 4 }
