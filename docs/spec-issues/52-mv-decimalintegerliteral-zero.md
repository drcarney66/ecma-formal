# 52. Static Semantics: MV has a row for `` DecimalIntegerLiteral :: `0` ``, a production the grammar does not have

- **Location:** §12.9.3 Numeric Literals (`#sec-literals-numeric-literals`), the production of
  |DecimalIntegerLiteral|, and §12.9.3.2 Static Semantics: MV (`#sec-static-semantics-mv`), its row for
  `` DecimalIntegerLiteral :: `0` ``.
- **Kind:** editorial (a stale row).
- **Model erratum:** `MVDecimalIntegerLiteralZero`, default reading literal; its readings: literal, proposed (delete
  the row). They agree on every program, as the row is never applied; the model records the row as one with no
  production (`emu-orphan-row` in `spec/formal/readings.emu`).
- **Upstream:** Checked 2026-11-19: none found (searched for "DecimalIntegerLiteral"). The row became stale with
  commit 78ea84c0f (PR #3988, merged 2026-10), "Editorial: Replace `0` and |NonZeroDigit| alternative productions with
  |DecimalDigit|", which changed the grammar and not the row.

## Text

§12.9.3:

> DecimalIntegerLiteral ::
>   DecimalDigit
>   NonZeroDigit NumericLiteralSeparator? DecimalDigits[+Sep]
>   NonOctalDecimalIntegerLiteral

§12.9.3.2 Static Semantics: MV:

> The MV of DecimalIntegerLiteral :: `0` is 0.

The production has no alternative `` `0` ``: the literal `0` is matched by its first alternative, |DecimalDigit|.

## Problem

Read literally, the row names no production of the grammar, so it is never applied. The literal `0` is an
instance of `DecimalIntegerLiteral :: DecimalDigit`, a chain production, whose MV is that of its |DecimalDigit|
(§5.2.3's implicit definition for chain productions), which is 0. Nothing observable depends on the row: `0`, `0.5`,
`0e1` and `0n` have the same values with it or without it.

The row is a stale equation: an operation defined for a production that does not exist. A reader, or a tool that
reads the grammar and the static semantics of spec.html together, has to decide what it means.

## Proposed wording

Proposed: delete the row.

```diff
--- a/spec.html
+++ b/spec.html
@@ -17232,9 +17232,6 @@
             The MV of <emu-grammar>DecimalLiteral :: DecimalIntegerLiteral ExponentPart</emu-grammar> is the MV of |DecimalIntegerLiteral| × 10<sup>_e_</sup>, where _e_ is the MV of |ExponentPart|.
           </li>
           <li>
-            The MV of <emu-grammar>DecimalIntegerLiteral :: `0`</emu-grammar> is 0.
-          </li>
-          <li>
             The MV of <emu-grammar>DecimalIntegerLiteral :: NonZeroDigit NumericLiteralSeparator? DecimalDigits</emu-grammar> is (the MV of |NonZeroDigit| × 10<sup>_n_</sup>) + the MV of |DecimalDigits|, where _n_ is the number of code points in |DecimalDigits|, excluding all occurrences of |NumericLiteralSeparator|.
           </li>
           <li>
```

## test262

No test is affected: the literal `0` has the MV 0 with or without the row.
