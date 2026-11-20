# 07. TypedArray `with` and `filter` assert that a BigInt store of *undefined* succeeds

The pinned text no longer has this defect: filter and with now perform `?` TypedArraySetElement, and the model's
errata `TypedArrayWithSetElementAbrupt` and `TypedArrayFilterKeptUndefined` are retired.

- **Location:** §23.2.3.10 %TypedArray%.prototype.filter (`#sec-%typedarray%.prototype.filter`), step 11.b (before
  the fix: step 11.a), and §23.2.3.36 %TypedArray%.prototype.with (`#sec-%typedarray%.prototype.with`), step 10.d
  (before the fix: step 10.c), with §10.4.5.18 TypedArraySetElement (`#sec-typedarraysetelement`), step 1, and
  §10.4.5.17 TypedArrayGetElement (`#sec-typedarraygetelement`), step 1.
- **Kind:** failing `!` (fixed).
- **Model erratum:** none: `TypedArrayWithSetElementAbrupt` and `TypedArrayFilterKeptUndefined` are retired, and
  the model runs the pinned text as written. Their test262 reading was the text that is now pinned.
- **Upstream:** Checked 2026-11-19: fixed. Issue #3978 (closed, 2026-09), "TypedArray copy methods can reach abrupt
  element writes after RAB shrink", reported it; PR #3979, "Editorial: fix incorrect assertion in
  TA.prototype.{filter,with}", merged 2026-10-16 as commit 4feb0272b, replaced both `!` by `?`.

## Text

filter, as pinned:

> 9. Let _result_ be ? TypedArraySpeciesCreate(_obj_, « 𝔽(_captured_) »).
> 10. Let _n_ be 0.
> 11. For each element _element_ of _kept_, do
>     a. NOTE: _element_ may be *undefined* if invoking _callback_ detaches or shrinks the buffer backing _obj_.
>     b. Perform ? TypedArraySetElement(_result_, 𝔽(_n_), _element_).

with, as pinned:

> 10. Repeat, while _k_ < _length_,
>     a. If _k_ = _actualIndex_, let _fromValue_ be _numericValue_.
>     b. Else, let _fromValue_ be TypedArrayGetElement(_obj_, 𝔽(_k_)).
>     c. NOTE: _fromValue_ may be *undefined* if either _index_ or _value_ is an object that runs code when coerced
>        to a Number or a BigInt and that code shrinks the buffer backing _obj_.
>     d. Perform ? TypedArraySetElement(_resultArray_, 𝔽(_k_), _fromValue_).

Before the fix, the two NOTEs were absent and the steps were filter 11.a and with 10.c:

<!-- quote: ECMA-262 before the fix -->
> 11.a. Perform ! TypedArraySetElement(_result_, 𝔽(_n_), _element_).
>
> 10.c. Perform ! TypedArraySetElement(_resultArray_, 𝔽(_k_), _fromValue_).

TypedArraySetElement and TypedArrayGetElement (unchanged):

> 1. If _obj_.[[ContentType]] is ~bigint~, let _number_ be ? ToBigInt(_value_).
>
> 1. If IsValidIntegerIndex(_obj_, _index_) is *false*, return *undefined*.

## Problem

User code can shrink a resizable buffer between a read and the store that copies it: filter's _callback_ (the
elements it reads after the shrink are *undefined* and may be kept), and with's coercions of _index_ and _value_
(steps 4–6, before the loop's TypedArrayGetElement reads past the new length). The stored value is then
*undefined*. For a BigInt64Array or BigUint64Array, TypedArraySetElement's ToBigInt(*undefined*) throws a
*TypeError*, so the `!` of filter's step 11.a and with's step 10.c, before the fix, asserted a completion that is
abrupt. (For the Number types, ToNumber(*undefined*) is *NaN* and the store succeeds.)

## Examples

[examples/07-typedarray-with-filter-bang.js](examples/07-typedarray-with-filter-bang.js) (outputs:
[RESULTS.md](examples/RESULTS.md#07-typedarray-with-filter-bangjs)):

```js
var rab = new ArrayBuffer(16, { maxByteLength: 16 });
var ta = new BigInt64Array(rab);
try {
  ta.with(0, { valueOf() { rab.resize(8); return 0n; } });
  print("with: no exception");
} catch (e) { print("with: " + e.constructor.name); }
var rab2 = new ArrayBuffer(16, { maxByteLength: 16 });
var tb = new BigInt64Array(rab2);
var calls = 0;
try {
  tb.filter(function () { calls++; rab2.resize(8); return true; });
  print("filter: no exception");
} catch (e) { print("filter: " + e.constructor.name + " after " + calls + " calls"); }
```

| | `with` | `filter` |
|---|---|---|
| the text before the fix | with 10.c's `!` fails (_k_ = 1) | filter 11.a's `!` fails (_n_ = 1), after 2 calls |
| the pinned text | `TypeError` | `TypeError after 2 calls` |
| V8, SpiderMonkey | `TypeError` | `TypeError after 2 calls` |
| JavaScriptCore | `TypeError` | `no exception` |
| formal model (the pinned text) | `TypeError` | `TypeError after 2 calls` |

JavaScriptCore's `filter` disagrees with both texts; it fails the test262 test below.

## test262

`built-ins/TypedArray/prototype/filter/BigInt/callbackfn-shrink-kept-undefined.js` (a *TypeError* after all
callbacks), and `built-ins/TypedArray/prototype/with/BigInt/index-coercion-shrinks.js` and
`…/with/BigInt/value-coercion-shrinks.js` (a *TypeError*) require the pinned text. They fail under the text before
the fix.
