# 25. `1 << 31`: Number::leftShift, the right shifts and bitwiseNOT say "a shift of a Number" without fixing its width

- **Location:** §6.1.6.1.9 Number::leftShift (`#sec-numeric-types-number-leftShift`), §6.1.6.1.10
  Number::signedRightShift (`#sec-numeric-types-number-signedRightShift`), §6.1.6.1.11 Number::unsignedRightShift
  (`#sec-numeric-types-number-unsignedRightShift`), step 4 of each; §6.1.6.1.2 Number::bitwiseNOT
  (`#sec-numeric-types-number-bitwiseNOT`), step 2.
- **Kind:** editorial: an irregular step (a result defined by an informal operation plus a range sentence). No
  defect: read whole, with the range sentence fixing the 32-bit view, the text gives the results below.
- **Model erratum:** none: the model reads the steps whole, with the range sentence fixing the 32-bit view (register
  row `number-shift-width`, `spec/formal/decisions.md`).
- **Upstream:** Checked 2026-11-19: PR #2274 (open, a draft, 2021-01), "Editorial: Express some 'bitwise' Number
  methods more explicitly", rewrites these four steps over 32-bit bit strings (NumberToInt32Bits, then
  Int32BitsToNumber or Uint32BitsToNumber), the change proposed here; it is not merged. PR #3987 (merged 2026-10,
  commits 02f2b1fad and 40ce6f206) changed only `&`, `|` and `^`.

## Text

Number::leftShift:

> 4. Return the result of left shifting _leftNumber_ by _shiftCount_ bits. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string.

Number::signedRightShift:

> 4. Return the result of performing a sign-extending right shift of _leftNumber_ by _shiftCount_ bits. The most significant bit is propagated. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string.

Number::unsignedRightShift:

> 4. Return the result of performing a zero-filling right shift of _leftNumber_ by _shiftCount_ bits. Vacated bits are filled with zero. The mathematical value of the result is exactly representable as a 32-bit unsigned bit string.

Number::bitwiseNOT:

> 2. Return the bitwise complement of _oldValue_. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string.

## Why it is irregular

The operand is a Number, and "left shifting _leftNumber_ by _shiftCount_ bits" is not defined for a Number anywhere.
Only the trailing sentence implies a 32-bit width, and it reads as a claim about the result rather than as the
operation's definition. Read as arithmetic, `1 << 31` is 2<sup>31</sup>, which the sentence says is not
representable, so the step contradicts itself. Read as an operation on the 32-bit two's complement bit string of
_leftNumber_, the result is -2<sup>31</sup>. Only the second reading is consistent, and it is what test262 requires
and the model computes; the text is unclear, not wrong. For the right shifts and NOT, both readings agree, but "a
sign-extending right shift of _leftNumber_" and "the bitwise complement of _oldValue_" also lean on the unstated
bit-string view.

NumberBitwiseOp (§6.1.6.1.16, `#sec-numberbitwiseop`) already spells its bit strings out ("the 32-bit two's
complement bit string representing ℝ(_leftNumber_)"), and BigInt::leftShift (§6.1.6.2.9,
`#sec-numeric-types-bigint-leftShift`) uses arithmetic: `ℤ(floor(ℝ(_x_) / 2^-ℝ(_y_)))`.

## Examples

| | `1 << 31` | `3 << 33` | `-9 >> 1` | `-1 >>> 28` | `~5` |
|---|---|---|---|---|---|
| arithmetic reading | 2147483648 (contradicts the range sentence) | 6 | -5 | 15 | -6 |
| bit-string reading, test262 | -2147483648 | 6 | -5 | 15 | -6 |
| formal model | -2147483648 | 6 | -5 | 15 | -6 |

The model's row is `print([1 << 31, 3 << 33, -9 >> 1, -1 >>> 28, ~5].join(" "))` run with `ecma-run`.

## Proposed wording

Proposed, in the style of ToInt32 and BigInt::leftShift, with no bit strings (ToFixedSizeInteger is §7.1.7,
`#sec-tofixedsizeinteger`):

```diff
 Number::leftShift
-        1. Return the result of left shifting _leftNumber_ by _shiftCount_ bits. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string.
+        1. Return 𝔽(ToFixedSizeInteger(ℝ(_leftNumber_) × 2<sup>_shiftCount_</sup>, ~signed~, 32)).
 Number::signedRightShift
-        1. Return the result of performing a sign-extending right shift of _leftNumber_ by _shiftCount_ bits. The most significant bit is propagated. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string.
+        1. Return 𝔽(floor(ℝ(_leftNumber_) / 2<sup>_shiftCount_</sup>)).
 Number::unsignedRightShift
-        1. Return the result of performing a zero-filling right shift of _leftNumber_ by _shiftCount_ bits. Vacated bits are filled with zero. The mathematical value of the result is exactly representable as a 32-bit unsigned bit string.
+        1. Return 𝔽(floor(ℝ(_leftNumber_) / 2<sup>_shiftCount_</sup>)).
 Number::bitwiseNOT
-        1. Return the bitwise complement of _oldValue_. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string.
+        1. Return 𝔽(-ℝ(_oldValue_) - 1).
```

In signedRightShift, _leftNumber_ is ToInt32's result, so floor division is the
sign-extending shift. In unsignedRightShift, it is ToUint32's result
(non-negative), so floor division is the zero-filling shift. The alternative
is NumberBitwiseOp's style, with bit strings and a defined shift on them, but
that needs the shift on bit strings defined first.

## test262

`language/expressions/left-shift/S11.7.1_A4_T4.js` (its check #994: `1 << 31 === -2147483648`), and the S9.5/S9.6
tests of `<<`, `>>>` and `~` (in `left-shift/`, `unsigned-right-shift/` and `bitwise-not/`).
