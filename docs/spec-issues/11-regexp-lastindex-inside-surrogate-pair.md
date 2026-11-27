# 11. `/u` with `lastIndex` inside a surrogate pair: a match reported one code unit late, and a Match Record that ends before it starts

- **Location:** §22.2.7.2 RegExpBuiltinExec (`#sec-regexpbuiltinexec`), steps 13.b, 15, 22, 24 and 28; §22.2.7.5
  Match Records (`#sec-match-records`); §22.2.7.6 GetMatchString (`#sec-getmatchstring`), step 1 (also §22.2.7.7
  GetMatchIndexPair (`#sec-getmatchindexpair`), step 1).
- **Kind:** a result that every engine tried contradicts (and on which they disagree), and, for an empty match, an
  ill-formed Match Record and a failing Assert.
- **Model erratum:** `GetMatchStringStartAfterEnd`, baked-in SpecTec reading literal on `GetMatchString` step 1's
  `Assert:`, paired with a non-literal reading baked into `@ph-input-index-of` (`spec/spectec/clauses/Helpers.spectec`)
  for `RegExpBuiltinExec` step 13.b: `@ph-input-index-of` maps a trailing-surrogate `_lastIndex_` backward to the code-point
  index of the containing surrogate pair (and returns `$ListLen(_input_)` at `_lastIndex_ == _length_`, see
  [59](59-regexp-exec-end-of-string.md)). Because `_lastIndex_` itself is not moved back, an empty match (`/(?:)/gu`)
  stops at `GetMatchString` step 1, while a non-empty match (`/./gu` at `lastIndex = 1` on `"\u{1F600}x"`) returns the
  lone trailing surrogate `"\uDE00"` at `index: 1`. The proposed reading moves `_lastIndex_` back to the start of the
  code point as well.
- **Upstream:** Checked 2026-11-19: issue #128 (open, 2015-10), "Unicode RegExp with index points trail surrogate in
  surrogate pair is not covered in the spec", and issue #2511 (open, 2021-09), "Underspecified behavior of global
  unicode regular expressions with lastIndex inside a surrogate pair", ask what the index of step 13.b means inside a
  pair; on #2511 (2021-09-11) the author of that step's wording answered that it refers to the code point of the pair,
  and #2511 was called a duplicate of #128.

## Text

RegExpBuiltinExec:

> 13. Repeat, while _matchSucceeded_ is *false*,
>     b. Let _inputIndex_ be the index into _input_ of the character that was obtained from element _lastIndex_ of
>        _string_.
>     c. Let _result_ be _matcher_(_input_, _inputIndex_).
> 14. Let _endIndex_ be _result_.[[EndIndex]].
> 15. If _fullUnicode_ is *true*, set _endIndex_ to GetStringIndex(_string_, _endIndex_).
> 16. If _global_ is *true* or _sticky_ is *true*, then
>     a. Perform ? Set(_regexp_, *"lastIndex"*, 𝔽(_endIndex_), *true*).
> …
> 22. Perform ! CreateDataPropertyOrThrow(_array_, *"index"*, 𝔽(_lastIndex_)).
> …
> 24. Let _match_ be the Match Record { [[StartIndex]]: _lastIndex_, [[EndIndex]]: _endIndex_ }.
> …
> 28. Let _matchedSubstring_ be GetMatchString(_string_, _match_).

The Match Record table gives [[EndIndex]] the value "an integer ≥ [[StartIndex]]". GetMatchString: "1. Assert:
_match_.[[StartIndex]] ≤ _match_.[[EndIndex]] ≤ the length of _string_."

## Problem

With the u or v flag, _input_ is the String's code points. When _lastIndex_ is the index of the trailing surrogate of
a pair, step 13.b gives the code point that contains it, which begins one code unit earlier. Nothing moves
_lastIndex_ back with it, and steps 22 and 24 report the match from _lastIndex_:

- **A non-empty match.** `/./gu` with `lastIndex = 1` on `"\u{1F600}x"` matches the code point U+1F600, so
  _endIndex_ is 2. Step 22 reports `index` 1, and step 28's _matchedSubstring_ is the substring from 1 to 2, the
  lone trailing surrogate 0xDE00. No Assert is involved; every engine tried contradicts this result.
- **An empty match.** If the pattern matches the empty String there, _endIndex_ is the start of that code point,
  _lastIndex_ - 1, and step 24 builds the Match Record { [[StartIndex]]: _lastIndex_, [[EndIndex]]: _lastIndex_ - 1
  }, which the Match Record table does not allow. Step 28's GetMatchString Assert fails (with the d flag,
  GetMatchIndexPair's too).

## Examples

[examples/11-regexp-lastindex-inside-surrogate-pair.js](examples/11-regexp-lastindex-inside-surrogate-pair.js)
(outputs: [RESULTS.md](examples/RESULTS.md#11-regexp-lastindex-inside-surrogate-pairjs)):

```js
var n = /./gu;
n.lastIndex = 1;
var mn = n.exec("\u{1F600}x");
print("non-empty: index " + mn.index + ", match length " + mn[0].length +
  ", first unit " + mn[0].charCodeAt(0).toString(16) + ", lastIndex " + n.lastIndex);
var r = /(?:)/gu;
r.lastIndex = 1;
var m = r.exec("\u{1F600}");
print("empty: index " + m.index + ", match length " + m[0].length + ", lastIndex " + r.lastIndex);
var rd = /(?:)/gud;
rd.lastIndex = 1;
var md = rd.exec("\u{1F600}");
print("indices[0] " + JSON.stringify(md.indices[0]));
```

| | non-empty | empty | `indices[0]` |
|---|---|---|---|
| literal text | `index 1, match length 1, first unit de00, lastIndex 2` | GetMatchString's Assert fails ({ [[StartIndex]]: 1, [[EndIndex]]: 0 }) | (not reached) |
| V8, SpiderMonkey | `index 0, match length 2, first unit d83d, lastIndex 2` | `index 0, match length 0, lastIndex 0` | `[0,0]` |
| JavaScriptCore | `index 2, match length 1, first unit 78, lastIndex 3` | `index 1, match length 0, lastIndex 1` | `[1,1]` |
| formal model (literal reading) | (not printed) | stops at GetMatchString step 1 | (not printed) |
| formal model (proposed reading) | `index 0, match length 2, first unit d83d, lastIndex 2` | `index 0, match length 0, lastIndex 0` | `[0,0]` |

V8 and SpiderMonkey start the match, and report it, at the start of the code point that contains _lastIndex_ (index
0). JavaScriptCore does not match the code point that begins before _lastIndex_: its non-empty match is the next code
point (`x`, at index 2), and its empty match lies at index 1, between the two code units of the pair, a position that
the code-point _input_ does not have. No engine produces the literal result. SpecTec stops at
GetMatchString step 1 (`stop: assertFailed sec-getmatchstring#0 1`) on the empty-match case, and a run that stops
reports only the stop; under the proposed reading below it prints V8's
and SpiderMonkey's lines.

## Proposed wording

Proposed: start the match, and report it, at the first code unit of the code point, as V8 and SpiderMonkey do. This
fixes both cases. (The other repair, moving _lastIndex_ forward to the next code-point boundary, is JavaScriptCore's
non-empty result; its empty match would then be at index 2.)

```diff
--- a/spec.html
+++ b/spec.html
@@ -39823,6 +39823,7 @@
                 1. Perform ? <emu-meta suppress-effects="user-code">Set(_regexp_, *"lastIndex"*, *+0*<sub>𝔽</sub>, *true*)</emu-meta>.
               1. Return *null*.
             1. Let _inputIndex_ be the index into _input_ of the character that was obtained from element _lastIndex_ of _string_.
+            1. If _fullUnicode_ is *true*, set _lastIndex_ to GetStringIndex(_string_, _inputIndex_).
             1. Let _result_ be _matcher_(_input_, _inputIndex_).
             1. If _result_ is ~failure~, then
               1. If _sticky_ is *true*, then
```

## test262

No test sets `lastIndex` inside a surrogate pair before a /u match. `built-ins/RegExp/prototype/exec/u-lastindex-adv.js`
and `built-ins/RegExp/prototype/Symbol.split/u-lastindex-adv-thru-*.js` advance through pairs with
AdvanceStringIndex, which never stops inside one.
