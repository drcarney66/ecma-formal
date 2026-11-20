// IteratorDestructuringAssignmentEvaluation (§13.15.5.5) of the productions
// AssignmentElementList : AssignmentElisionElement and AssignmentElisionElement :
// AssignmentElement, whose algorithms are one step each (their binding
// counterparts have none), in a list with and without elisions, and nested.
// sections: sec-runtime-semantics-iteratordestructuringassignmentevaluation sec-runtime-semantics-destructuringassignmentevaluation
// expect: sec-runtime-semantics-iteratordestructuringassignmentevaluation 1. Return ? IteratorDestructuringAssignmentEvaluation of AssignmentElisionElement with argument iteratorRecord.
// expect: sec-runtime-semantics-iteratordestructuringassignmentevaluation 1. Return ? IteratorDestructuringAssignmentEvaluation of AssignmentElement with argument iteratorRecord.
// expect: sec-runtime-semantics-iteratordestructuringassignmentevaluation 2. Return ? IteratorDestructuringAssignmentEvaluation of AssignmentElisionElement with argument iteratorRecord.
// expect: sec-runtime-semantics-iteratordestructuringassignmentevaluation 1. Perform ? IteratorDestructuringAssignmentEvaluation of Elision with argument iteratorRecord.
function plain() {
  Math.max();
  var a, b, c, o = {};
  [a, , b = void 1, ...c] = [1, 2];
  ({ b: [c] = [void 2] } = o);
  [, a] = [void 3, 4];
  Math.min();
}
function* gen() {
  Math.max();
  var a, b, c, o = {};
  [a, , b = yield 1, ...c] = [1, 2];
  ({ b: [c] = [yield 2] } = o);
  [, a] = [yield 3, 4];
  Math.min();
}
