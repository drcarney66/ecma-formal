# 51. A maximum BigInt size: `2n ** (2n ** 40n)` has an exact result in the text, which allows no maximum size

- **Location:** §6.1.6.2 The BigInt Type (`#sec-ecmascript-language-types-bigint-type`), its first paragraph;
  §6.1.6.2.3 BigInt::exponentiate (`#sec-numeric-types-bigint-exponentiate`), step 3; §6.1.6.2.4 BigInt::multiply
  (`#sec-numeric-types-bigint-multiply`), step 1, and its note; §6.1.6.2.7 BigInt::add (`#sec-numeric-types-bigint-add`), step 1;
  §6.1.6.2.8 BigInt::subtract (`#sec-numeric-types-bigint-subtract`), step 1; §6.1.6.2.9 BigInt::leftShift
  (`#sec-numeric-types-bigint-leftShift`), step 2; §21.2.2.2 BigInt.asUintN (`#sec-bigint.asuintn`), step 3.
- **Kind:** proposed normative change (not a defect: the text is consistent and gives every result).
- **Model erratum:** `BigIntMaximumSize`, default reading proposed; its readings: literal, proposed. The proposed
  reading asks the host, before the result is formed, whether it would exceed the implementation's maximum (the
  host primitive BigIntTooLarge, `spec/formal/numbers.emu`; the model's host answers *true* past 2<sup>30</sup>
  bits, covering `exponentiate`, `leftShift`, `multiply`, `add`, `subtract`, and `asUintN`) and throws a *RangeError*
  if so; the literal reading forms the result whatever its size.
- **Upstream:** Checked 2026-11-19: none found that proposes this (searched for BigInt with "maximum size" and with
  "size limit"). Related: issue #1391 (open, 2019-01), "Extending defining out-of-memory beyond ArrayBuffer", asks
  whether BigInt will have a defined out-of-memory error as ArrayBuffer has; issue #4063 (closed, 2026-10, as not
  planned), "Specify that exceeding resource limits may throw", asked it of resource limits in general.

## Text

§6.1.6.2:

> The BigInt type represents an integer value. The value may be any size and is not limited to a particular
> bit-width.

BigInt::exponentiate:

> 1. If _exponent_ < *0*ℤ, throw a *RangeError* exception.
> 2. If _base_ = *0*ℤ and _exponent_ = *0*ℤ, return *1*ℤ.
> 3. Return _base_ raised to the power _exponent_.

BigInt::multiply, with its note:

> 1. Return _x_ × _y_.

> Even if the result has a much larger bit width than the input, the exact mathematical answer is given.

BigInt::leftShift:

> 1. If _y_ < *0*ℤ, then
>    a. Return ℤ(floor(ℝ(_x_) / 2<sup>-ℝ(_y_)</sup>)).
> 2. Return _x_ × *2*ℤ<sup>_y_</sup>.

## Problem

The three operations are the ones whose result can be far larger than their operands, and each returns its exact
result, of any size. An implementation can hold BigInts only up to some size. Read as written,
`2n ** (2n ** 40n)` is 2<sup>2<sup>40</sup></sup>, a BigInt of 2<sup>40</sup> + 1 bits (about 137 GB), and a
conforming implementation must produce it; one that throws a *RangeError* there departs from the text: a search of
spec.html found no sentence that sets or allows a limit on the size of a BigInt.

The proposal is to say what an implementation with a limit does. In each of the three, before its result is formed, the proposed
step:

<!-- quote: the proposed step, not the text of spec.html -->
> If the result would exceed the implementation's maximum BigInt size, throw a *RangeError* exception.

The maximum stays implementation-defined. The change is normative: it makes a *RangeError* a conforming result
where the text now requires the exact BigInt.

The proposed wording below does not settle every consequence. BigInt::multiply, BigInt::add, BigInt::subtract, and
BigInt::leftShift return "a BigInt" and would return a completion record (their headers and their rows in §6.1.6's
Numeric Type Operations table); ApplyStringOrNumericBinaryOperator (§13.15.3) calls them in its last step, "Return
_operation_(_leftNumber_, _rightNumber_)", which would take `?`; BigInt::signedRightShift calls
BigInt::leftShift(_x_, -_y_), which shifts right and cannot exceed the maximum, so it would take `!`; and the
note of BigInt::multiply would end "unless it exceeds the implementation's maximum BigInt size". Under `BigIntMaximumSize`,
`BigInt.asUintN`, `BigInt::add`, and `BigInt::subtract` are covered alongside `exponentiate`, `leftShift`, and
`multiply`.

## Examples

No example program is in [examples/](examples/) for this proposal, and no engine's output is recorded in
RESULTS.md for it.

```js
try { print((2n ** (2n ** 40n)) > 0n); } catch (e) { print("**: " + e.constructor.name); }
try { print((1n << (2n ** 40n)) > 0n); } catch (e) { print("<<: " + e.constructor.name); }
var big = 1n << (2n ** 29n);
try { print((big * big * big) > 0n); } catch (e) { print("*: " + e.constructor.name); }
```

| | `**` | `<<` | `*` |
|---|---|---|---|
| literal text | `true` (an exact result of 2<sup>40</sup> + 1 bits) | `true` (likewise) | `true` (about 3 × 2<sup>29</sup> bits) |
| proposed text | `RangeError` where the result exceeds the implementation's maximum | likewise | likewise |
| formal model, proposed reading (the default) | `**: RangeError` | `<<: RangeError` | `*: RangeError` |

The model was not run under its literal reading here: it would have to form a BigInt of 2<sup>40</sup> + 1 bits.
The model's tests `tests/run/bigint_huge_power.js` (`3n ** (1n << 40n)`) and `tests/run/bigint_huge_left_shift.js`
(`2n << (1n << 64n)`) end `throw: RangeError` under the default reading, and `tests/run/bigint_power_below_limit.js`
computes `3n ** 5592406n` (8863754 bits), below the model's limit.

## Proposed wording

Proposed: the three steps (the consequences above are not drafted):

```diff
--- a/spec.html
+++ b/spec.html
@@ -2263,3 +2263,4 @@
             1. If _exponent_ &lt; *0*<sub>ℤ</sub>, throw a *RangeError* exception.
             1. If _base_ = *0*<sub>ℤ</sub> and _exponent_ = *0*<sub>ℤ</sub>, return *1*<sub>ℤ</sub>.
+            1. If the result would exceed the implementation's maximum BigInt size, throw a *RangeError* exception.
             1. Return _base_ raised to the power _exponent_.
@@ -2278,3 +2279,4 @@
           <emu-alg>
+            1. If the result would exceed the implementation's maximum BigInt size, throw a *RangeError* exception.
             1. Return _x_ × _y_.
           </emu-alg>
@@ -2358,3 +2360,4 @@
               1. Return ℤ(floor(ℝ(_x_) / 2<sup>-ℝ(_y_)</sup>)).
+            1. If the result would exceed the implementation's maximum BigInt size, throw a *RangeError* exception.
             1. Return _x_ × *2*<sub>ℤ</sub><sup>_y_</sup>.
           </emu-alg>
```

## test262

A search of test262 at 2e58f87d (exponentiations, shifts and products of huge BigInts, and "maximum BigInt size")
found no test that requires either the exact result or a *RangeError* past a limit.
