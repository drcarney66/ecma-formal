# 42. Annex B: "parsing source text using the goal symbol |Module|" and the parses within a Module

- **Location:** §B.1.1 HTML-like Comments (`#sec-html-like-comments`), its first paragraph, and §17.1 Forbidden
  Extensions (`#sec-forbidden-extensions`), with §5.1.5 The Syntactic Grammar (`#sec-syntactic-grammar`), the
  definition of "must cover".
- **Kind:** clarification (the text's results are definite; its condition is stated for one kind of parse only).
- **Model erratum:** none, since the text's results are definite: the model's parser invocations carry whether they
  are within a Module, set for the goal |Module| and inherited by a reparse of a node that invocation made.
- **Upstream:** Checked 2026-11-19: none found (searched for "HTML-like comments" with Module; the one hit, issue
  #1595 (open, 2019-06), "Annex B reform next steps", does not raise it in its description).

## Text

§B.1.1 (its "…" is a cross-reference to §12.4 Comments):

> The syntax and semantics of … is extended as follows except that this extension is not allowed when parsing
> source text using the goal symbol |Module|:

§17.1 (its "…" is a cross-reference to §B.1.1):

> When parsing for the |Module| goal symbol, the lexical grammar extensions defined in … must not be supported.

§5.1.5, the second item of the definition of "_p_ must cover an _n_":

> The sequence of tokens originally matched by _p_ is parsed again using _n_ as the goal symbol.

## The question

The condition names the goal symbol of the parse. Inside a Module there are parses with other goals: the
supplemental-grammar parses of §5.1.5 ("must cover", "covered by") and the early-error rules that parse a node
again. §5.1.5 says (above) that these parse again the sequence of tokens originally matched, so B.1.1, a lexical extension, does
not bear on them: the tokens are the Module's, scanned without it. The text gives that answer, but only through
§5.1.5's word "tokens"; an implementation (or a model) that reparses a node's source text has to carry "within a Module" to the reparse itself, or `<!--` changes meaning:

```js
// a Module
var a = 1, b = 2;
var x = (a <!--b);
```

The Module's tokens are `(` `a` `<` `!` `--` `b` `)`, a valid ParenthesizedExpression (`x` is *false*). Rescanned
with B.1.1, the cover's text `(a <!--b)` is `(a` and a comment, and the reparse fails.

The formal model, with §B.1.1 on (`ecma-run --module --annex-b sec-html-like-comments`), gives `x` the value *false* in
this Module (run with `print(x)` added); the same source run as a Script, where B.1.1 applies, is a SyntaxError.

Parses of new source text are not affected: eval code and the Function constructor's text are parsed as Scripts
(B.1.1 applies), whatever code calls them.

## Proposed wording

None is needed for the results. Proposed, to make the scope explicit, a note under §B.1.1:

```diff
--- a/spec.html
+++ b/spec.html
@@ -53808,1 +53808,4 @@
       <p>The syntax and semantics of <emu-xref href="#sec-comments"></emu-xref> is extended as follows except that this extension is not allowed when parsing source text using the goal symbol |Module|:</p>
+      <emu-note>
+        <p>The parses of <emu-xref href="#sec-syntactic-grammar"></emu-xref> that parse again a sequence of tokens matched within a |Module| read those tokens; this extension does not apply to them.</p>
+      </emu-note>
```
