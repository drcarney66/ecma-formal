// The `while` and `do`-`while` statements (§14.7.3.2, §14.7.2.2): test and
// body suspending.
// sections: sec-runtime-semantics-whileloopevaluation sec-runtime-semantics-dowhileloopevaluation sec-runtime-semantics-loopevaluation sec-runtime-semantics-labelledevaluation
function plain() {
  Math.max();
  var i = 0;
  while (i++ < 2) void i;
  while (void i) 0;
  do void i; while (i-- > 0);
  do 0; while (void i);
  Math.min();
}
function* gen() {
  Math.max();
  var i = 0;
  while (i++ < 2) yield i;
  while (yield i) 0;
  do yield i; while (i-- > 0);
  do 0; while (yield i);
  Math.min();
}
