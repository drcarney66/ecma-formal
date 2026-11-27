# 53. String operations omit `> 2^53 - 1` length checks required by §6.1.4's maximum String length

- **Location:** §6.1.4 The String Type (`#sec-ecmascript-language-types-string-type`), first paragraph; §22.1.3.18
  `String.prototype.repeat` (`#sec-string.prototype.repeat`), step 7; §22.1.3.5 `String.prototype.concat`
  (`#sec-string.prototype.concat`), step 5.b; §13.15.3 ApplyStringOrNumericBinaryOperator
  (`#sec-applystringornumericbinaryoperator`), step 1.c.iii; §23.1.3.18.1 JoinIndexedProperties
  (`#sec-joinindexedproperties`), steps 4.a and 4.d.iii.
- **Kind:** contradiction (operations form String values exceeding §6.1.4's `2^53 - 1` maximum length without throwing a
  *RangeError*).
- **Model erratum:** `StringLengthOverflow`, baked-in SpecTec reading proposed (`$StringTooLarge` in
  `spec/spectec/clauses/S13.spectec`, `S22.spectec`, `S23.spectec`, and `Host.ValueLaws.stringTooLarge` in
  `spec/spectec/prose/23-host-laws-values.spectec`, with `Engine.Host` answering `*true*` past `2^28` and therefore past
  `2^53 - 1`; for the smaller finite-memory host limit `2^28`, see [54](54-string-maximum-length.md)).
- **Upstream:** Checked 2026-11-20: none found for the missing `> 2^53 - 1` check in `repeat`, `concat`, `+` and
  `JoinIndexedProperties` (searched for String with "maximum length" and "RangeError"). Related: issue #4063 (closed,
  2026-10), "Specify that exceeding resource limits may throw".

## Text

§6.1.4:

> The String type is the set of all ordered sequences of zero or more 16-bit unsigned integer values (“elements”) up to a maximum length of 2<sup>53</sup> - 1 elements.

`String.prototype.repeat`:

> 5. If _n_ < 0 or _n_ = +∞, throw a *RangeError* exception.
> 6. If _n_ = 0, return the empty String.
> 7. Return the String value that is made from _n_ copies of _string_ appended together.

`String.prototype.concat`:

> b. Set _result_ to the string-concatenation of _result_ and _nextString_.

`ApplyStringOrNumericBinaryOperator`:

> iii. Return the string-concatenation of _leftString_ and _rightString_.

`JoinIndexedProperties`:

> a. If _k_ > 0, set _result_ to the string-concatenation of _result_ and _separator_.

> iii. Set _result_ to the string-concatenation of _result_ and _elementString_.

## Problem

§6.1.4 bounds every String value to at most 2<sup>53</sup> - 1 code units (while `StringPaddingBuiltinsImpl` clamps
`ToLength(_maxLength_)` to ≤ 2<sup>53</sup> - 1, and `Array.prototype.push` / `TypedArray` operations explicitly throw past
2<sup>53</sup> - 1).
However, `String.prototype.repeat`, `String.prototype.concat`, string `+` (`ApplyStringOrNumericBinaryOperator`), and
`JoinIndexedProperties` have no length check before forming their result:

- `"ab".repeat(2 ** 52)` passes step 5 (`_n_ = 2^52` is finite and non-negative), then step 7 asks for a String value of
  length `2^53 > 2^53 - 1`, which does not exist in §6.1.4's String type!
- Likewise, concatenating or joining two Strings whose lengths sum past `2^53 - 1` demands a String value outside the
  String type rather than throwing a *RangeError*.

## Examples

```js
try { "ab".repeat(2 ** 52); } catch (e) { print("repeat > 2^53-1: " + e.constructor.name); }
```

| | `"ab".repeat(2 ** 52)` |
|---|---|
| literal text | asks for a `2^53`-element String value, contradicting §6.1.4 |
| V8, SpiderMonkey, JavaScriptCore | `RangeError` |
| formal model (proposed reading) | `repeat > 2^53-1: RangeError` |

## Proposed wording

Before constructing the result String in `String.prototype.repeat` step 7 (`_n_ × the length of _string_`),
`String.prototype.concat` step 5.b, `ApplyStringOrNumericBinaryOperator` step 1.c.iii, and `JoinIndexedProperties` steps
4.a and 4.d.iii, throw a *RangeError* exception if the resulting length would exceed 2<sup>53</sup> - 1 (or the
implementation's smaller maximum String length; see [54](54-string-maximum-length.md)).

## test262

`built-ins/String/prototype/repeat/` tests negative and `+Infinity` counts (`repeat(-1)`, `repeat(Infinity)`), not finite
counts whose product with `_string_`'s length exceeds `2^53 - 1`.
