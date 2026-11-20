// Two GroupSpecifiers with one CapturingGroupName are a SyntaxError unless
// some Disjunction has them in different Alternatives (§22.2.1.1, Pattern ::
// Disjunction; MightBothParticipate, §22.2.1.4), in nested Disjunctions too,
// for new RegExp and for a RegularExpressionLiteral (§13.2.7.2).
// expect: normal: undefined
// print: SyntaxError SyntaxError SyntaxError ok ok
// print: SyntaxError
// print: y
function t(s) { try { new RegExp(s); return "ok"; } catch (e) { return e.name; } }
print(t("(?:(?<a>x)|y)(?:z|(?<a>w))") + " " + t("(?<a>x)(?:|(?<a>z))") + " " + t("(?<a>(?<a>x))") + " " +
  t("(?<a>x)|(?<a>y)") + " " + t("((?<a>x)|y|(?:z|(?<a>w)))"));
try { eval("/(?:(?<a>x)|y)(?:z|(?<a>w))\\k<a>/"); print("parsed"); } catch (e) { print(e.name); }
print(/(?:(?<a>x)|(?<a>y))\k<a>/.exec("yy").groups.a);
