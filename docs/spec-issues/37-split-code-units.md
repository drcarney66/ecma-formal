# 37. String.prototype.split with an empty separator builds an Array of code units

- **Location:** §22.1.3.23 String.prototype.split (`#sec-string.prototype.split`), steps 10.d–e and the method's
  description, against §7.3.17 CreateArrayFromList (`#sec-createarrayfromlist`), its parameter.
- **Kind:** type error (a List of code units where a List of ECMAScript language values is required).
- **Model erratum:** `SplitCodeUnitStrings`, default reading test262; its readings: literal, test262, proposed. The
  test262 and proposed readings are the same steps, the proposed wording below.
- **Upstream:** Checked 2026-11-19: none found (searched for split with "empty separator" and with "code units"). The
  List of code units came with PR #2144 (merged 2021-10, commit 82438c337); PR #2975 (merged 2026-10, commit
  cb866719b) rewrote the description and the notes, renamed _lim_, and left steps 10.d–e as they were; issue #3261
  (closed, 2024-08), ""substring of" used with potentially out of bounds end in String.prototype.split()", was about
  step 10.c.

## Text

> 10. If _separatorLength_ = 0, then
>     a. Let _stringLength_ be the length of _string_.
>     b. Let _outLength_ be the result of clamping _substringLimitInt_ between 0 and _stringLength_.
>     c. Let _head_ be the substring of _string_ from 0 to _outLength_.
>     d. Let _codeUnits_ be a List consisting of the sequence of code units that are the elements of _head_.
>     e. Return CreateArrayFromList(_codeUnits_).

CreateArrayFromList takes "_elements_: a List of ECMAScript language values", and the method's description says:
"This method finds substrings separated by _separator_ in its *this* value and returns them in an Array, … any
_separator_ coerced to the empty String splits the *this* value into individual code units, …".

## Problem

A code unit is one of the 16-bit unsigned integer values a String is a sequence of (§6.1.4), not an ECMAScript
language value. Step 10.e passes a List of them to CreateArrayFromList, outside its parameter's type, and the
Array it would build has elements that are not values: `typeof "ab".split("")[1]` has no defined result. The
description states the intent, substrings in an Array, here one String of one code unit per element, which step 10.d
does not say.

## Examples

[examples/37-split-code-units.js](examples/37-split-code-units.js) (outputs:
[RESULTS.md](examples/RESULTS.md#37-split-code-unitsjs)):

```js
var a = "ab".split("");
print(a.length + " " + typeof a[1] + " " + JSON.stringify(a));
print(new String(" ").split("")[0] === " ");
print(JSON.stringify("\u{1F600}".split("")));
```

| | `"ab".split("")` | `new String(" ").split("")[0] === " "` | `"\u{1F600}".split("")` |
|---|---|---|---|
| literal step 10.d | no defined result (the elements are code units) | no defined result | no defined result |
| V8, SpiderMonkey, JavaScriptCore | `2 string ["a","b"]` | `true` | `["\ud83d","\ude00"]` |
| formal model (test262 and proposed readings) | `2 string ["a","b"]` | `true` | `["\ud83d","\ude00"]` |
| formal model (literal reading) | the run stops at the `typeof` (`stop: sortError sec-typeof-operator-runtime-semantics-evaluation#0 13`) | — | — |

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -36559,7 +36559,9 @@
             1. Let _stringLength_ be the length of _string_.
             1. Let _outLength_ be the result of clamping _substringLimitInt_ between 0 and _stringLength_.
             1. Let _head_ be the substring of _string_ from 0 to _outLength_.
-            1. Let _codeUnits_ be a List consisting of the sequence of code units that are the elements of _head_.
+            1. Let _codeUnits_ be a new empty List.
+            1. For each integer _i_ such that 0 ≤ _i_ &lt; _outLength_, in ascending order, do
+              1. Append the substring of _head_ from _i_ to _i_ + 1 to _codeUnits_.
             1. Return CreateArrayFromList(_codeUnits_).
           1. If _string_ is the empty String, return CreateArrayFromList(« _string_ »).
           1. Let _substrings_ be a new empty List.
```

## test262

`built-ins/String/prototype/split/separator-empty-string-instance-is-string.js` requires `new String("
").split("")[0]` to be `" "`; seven more test files (three in the same directory, `RegExp/escape/not-escaped.js`,
`Iterator/zipKeyed/padding-iteration.js` and two in `staging/sm/String`) and the harness's `iteratorZipUtils.js`
use the elements of a `split("")` as Strings. All of them fail, or have no defined result, under the literal step.
