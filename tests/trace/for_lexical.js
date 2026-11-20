// A `for` statement with a LexicalDeclaration whose body suspends
// (ForLoopEvaluation §14.7.4.2, ForBodyEvaluation §14.7.4.3).
// sections: sec-runtime-semantics-forloopevaluation sec-forbodyevaluation sec-createperiterationenvironment sec-block-runtime-semantics-evaluation
function plain() {
  Math.max();
  for (let i = 0; i < 2; i++) void i;
  Math.min();
}
function* gen() {
  Math.max();
  for (let i = 0; i < 2; i++) yield i;
  Math.min();
}
