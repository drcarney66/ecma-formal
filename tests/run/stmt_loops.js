// Loops: LoopContinues and UpdateEmpty give a loop the value of its last
// non-empty iteration; `while (false)` is undefined.
// expect: normal: 3
1; while (false);
do { 3; break; } while (true)
