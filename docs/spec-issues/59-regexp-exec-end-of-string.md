# 59. `RegExpBuiltinExec` step 13.b indexes out-of-bounds `element _lastIndex_ of _string_` at end of string

- **Location:** §22.2.7.2 RegExpBuiltinExec (`#sec-regexpbuiltinexec`), steps 13.a and 13.b.
- **Kind:** undefined out-of-bounds element reference when `_lastIndex_ = _length_` (in both BMP and Unicode modes).
- **Model erratum:** `RegExpExecEndOfString`, baked-in SpecTec reading test262 (`@ph-input-index-of` in
  `spec/spectec/clauses/Helpers.spectec` and `S22.spectec`). When `_lastIndex_ == _length_`, `@ph-input-index-of`
  returns `$ListLen(_input_)` rather than indexing `_string_[_lastIndex_]`.
- **Upstream:** Checked 2026-11-19: none found for `_lastIndex_ = _length_` at step 13.b (issues #128 and #2511 concern
  surrogate pairs, see [11](11-regexp-lastindex-inside-surrogate-pair.md)).

## Text

`RegExpBuiltinExec`:

> 13. Repeat, while _matchSucceeded_ is *false*,
>     a. If _lastIndex_ > _length_, then
>        i. If _global_ is *true* or _sticky_ is *true*, then
>           1. Perform ? Set(_regexp_, *"lastIndex"*, *+0*<sub>𝔽</sub>, *true*).
>        ii. Return *null*.
>     b. Let _inputIndex_ be the index into _input_ of the character that was obtained from element _lastIndex_ of _string_.
>     c. Let _result_ be _matcher_(_input_, _inputIndex_).

## Problem

Step 13.a exits the loop only when `_lastIndex_ > _length_` (strictly greater, so empty matches such as `/(?:)/.exec("")`
and end-of-input assertions such as `/$/.exec("a")` can succeed at `_lastIndex_ = _length_`). At `_lastIndex_ = _length_`,
however, `_string_` has *no* element `_lastIndex_` (valid indices are `0` through `_length_ - 1`), and `_input_` has no
character at index `the number of elements in _input_`! Every global match that advances `_lastIndex_` to `_length_` (e.g.
the second `.exec("a")` call on `/a/g` or `/a/gu`) and every match on `""` reaches step 13.b with `_lastIndex_ = _length_`.

## Examples

```js
var r = /a/g;
print(r.exec("a")[0], r.lastIndex, r.exec("a"), r.lastIndex);
print(/(?:)/u.exec("")[0], /$/gu.exec("x").index);
```

| | second `/a/g.exec("a")` | `/(?:)/u.exec("")` | `/$/gu.exec("x").index` |
|---|---|---|---|
| literal step 13.b | undefined (`_string_[1]` on length-1 `"a"`) | undefined (`_string_[0]` on `""`) | undefined (`_string_[1]` on `"x"`) |
| V8, SpiderMonkey, JavaScriptCore | `null`, `lastIndex = 0` | `""` | `1` |
| formal model (test262 reading) | `null`, `lastIndex = 0` | `""` | `1` |

## Proposed wording

Guard step 13.b with: *"If _lastIndex_ = _length_, let _inputIndex_ be the number of elements in _input_; else let
_inputIndex_ be the index into _input_ of the character that was obtained from element _lastIndex_ of _string_."*

## test262

`built-ins/RegExp/prototype/exec/` tests global iteration to exhaustion (`null` at `_lastIndex_ = _length_`), empty
patterns on `""`, and `$` assertions at end of input.
