// expect: throw: SyntaxError
// `accessor` fields (the decorators proposal) are not ECMAScript: the source
// is a SyntaxError (jsparse exit 1, js-run exit 5; audit F084). Since F084 no
// source text reaches jsparse's exit 2 (a construct the Lean AST does not
// represent: only internal shapes), which js-run reports as `stop:
// unsupported jsparse: …` (exit 2, F335).
class A { accessor x }
