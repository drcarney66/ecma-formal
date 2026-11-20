# 41. Annex B: a first-line `-->` is an input element that is neither a comment nor a token

- **Location:** §B.1.1 HTML-like Comments (`#sec-html-like-comments`), InputElementHashbangOrRegExp's last
  alternative and the paragraph after the grammar, against §5.1.3 The Lexical and RegExp Grammars
  (`#sec-lexical-and-regexp-grammars`), its second paragraph.
- **Kind:** missing case (an input element the syntactic grammar has no terminal for).
- **Model erratum:** `HTMLCloseCommentToken`, default reading test262; its readings: literal, test262, proposed. The
  test262 and proposed readings read an |HTMLCloseComment| input element as a comment, which is the proposed wording
  below.
- **Upstream:** Checked 2026-11-19: none found (searched for "HTMLCloseComment"). The alternative came with PR #3244
  (merged 2024-02, commit 197f1245a), "Normative: Allow Annex B scripts to start with `-->`", with test262 PR #4002
  (merged 2024-02), "Add tests for `-->` in the first line"; the former changes only §B.1.1.

## Text

§B.1.1 extends §12.4 Comments:

> InputElementHashbangOrRegExp ::
>   WhiteSpace
>   LineTerminator
>   Comment
>   CommonToken
>   HashbangComment
>   RegularExpressionLiteral
>   HTMLCloseComment
>
> Comment ::
>   MultiLineComment
>   SingleLineComment
>   SingleLineHTMLOpenComment
>   SingleLineHTMLCloseComment
>   SingleLineDelimitedComment
>
> SingleLineHTMLCloseComment ::
>   LineTerminatorSequence HTMLCloseComment
>
> HTMLCloseComment ::
>   WhiteSpaceSequence? SingleLineDelimitedCommentSequence? `-->` SingleLineCommentChars?

and after the grammar: "Similar to a |MultiLineComment| that contains a line terminator code point, a
|SingleLineHTMLCloseComment| is considered to be a |LineTerminator| for purposes of parsing by the syntactic
grammar."

§5.1.3:

> Input elements other than white space and comments form the terminal symbols for the syntactic grammar for
> ECMAScript and are called ECMAScript *tokens*. … Simple white space and single-line comments are discarded and
> do not appear in the stream of input elements for the syntactic grammar.

## Problem

InputElementHashbangOrRegExp is the goal at the start of a Script (§12), and its new alternative makes an
|HTMLCloseComment| an input element of its own. It is not a |Comment| (|Comment|'s alternatives contain an
|HTMLCloseComment| only after a line terminator: in |SingleLineHTMLCloseComment|, or after a |MultiLineComment|
that contains one) and not white space, so §5.1.3 makes it a token, and no production of the syntactic grammar has
it as a terminal. Read literally, a Script whose first line is `--> a comment` has no parse and is a SyntaxError,
which is what the alternative was added to avoid; the section's title and its other productions make it a comment.

## Examples

[examples/41-annexb-html-close-comment-token.js](examples/41-annexb-html-close-comment-token.js) (outputs:
[RESULTS.md](examples/RESULTS.md#41-annexb-html-close-comment-tokenjs)):

```js
--> a comment: the first line is an HTMLCloseComment input element (B.1.1)
print("parsed");
```

| | output |
|---|---|
| literal text | SyntaxError (the first input element is a token no production has) |
| V8, SpiderMonkey, JavaScriptCore | `parsed` |
| formal model, §B.1.1 on (test262 and proposed readings) | `parsed` |
| formal model, §B.1.1 on (literal reading) | the run stops at the first line (`stop: residue formal-parsetextin#0 2`) |

The model's rows are `ecma-run --annex-b sec-html-like-comments`. Its run in RESULTS.md is on ecma-run's default
host, with Annex B off, where the first line is a SyntaxError under the main grammar, so it is not a witness here.

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -53863,6 +53863,7 @@
           SingleLineDelimitedComment WhiteSpaceSequence? SingleLineDelimitedCommentSequence?
       </emu-grammar>
       <p>Similar to a |MultiLineComment| that contains a line terminator code point, a |SingleLineHTMLCloseComment| is considered to be a |LineTerminator| for purposes of parsing by the syntactic grammar.</p>
+      <p>An |HTMLCloseComment| that is an input element is a comment: like a single-line comment, it is discarded and does not appear in the stream of input elements for the syntactic grammar.</p>
     </emu-annex>
 
     <emu-annex id="sec-regular-expressions-patterns">
```

Making |HTMLCloseComment| an alternative of |Comment| instead would let `-->` start a comment anywhere a |Comment|
may occur, mid-line included, which the section avoids.

## test262

`annexB/language/comments/single-line-html-close-first-line-1.js`, `-2.js` and `-3.js` (`--> a comment` on the first
line, after white space, and after two delimited comments) expect the Script to parse and then throw its own
EvalError at run time; under the literal text each is a SyntaxError and fails.
