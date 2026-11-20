// LabelledEvaluation: `break a` leaves both loops; `continue a` goes round the
// outer loop, whose value is the inner loop's 7.
// expect: normal: 7
a: for (;;) { for (;;) { break a; } }
a: do { do { 7; continue a; } while (true) } while (false)
