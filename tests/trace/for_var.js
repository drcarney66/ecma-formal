// A `for` statement with a `var` declaration whose body suspends (§14.7.4.2).
// sections: sec-runtime-semantics-forloopevaluation sec-forbodyevaluation sec-block-runtime-semantics-evaluation
function plain() {
  Math.max();
  for (var i = 0; i < 2; i++) void i;
  Math.min();
}
function* gen() {
  Math.max();
  for (var i = 0; i < 2; i++) yield i;
  Math.min();
}
