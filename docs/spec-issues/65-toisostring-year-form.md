# 65. `Date.prototype.toISOString` leaves 4-digit vs expanded `±YYYYYY` year format unspecified for `0..9999`

- **Location:** §21.4.4.36 `Date.prototype.toISOString` (`#sec-date.prototype.toisostring`), step 7, with §21.4.1.32
  Date Time String Format (`#sec-date-time-string-format`), `YYYY` and Expanded Years.
- **Kind:** underspecification (`test262` and all engines require 4-digit `YYYY` for years `0..9999`, whereas the prose
  permits `+002026`).
- **Model erratum:** `ToISOStringYearForm`, baked-in SpecTec reading test262 (`$ExpandedYearForm` in
  `spec/spectec/clauses/S21.spectec` and `lean/Engine/Host/Core.lean`). SpecTec binds `$ExpandedYearForm` to `false` for
  years in `0..9999` so `toISOString` always emits 4-digit `YYYY` there and 6-digit `±YYYYYY` outside `0..9999`.
- **Upstream:** Checked 2026-11-19: none found (searched for "toISOString" with "expanded year").

## Text

`Date.prototype.toISOString`:

> 7. Return a String representation of _tv_ in the Date Time String Format on the UTC time scale, including all format elements and the UTC offset representation *"Z"*.

§21.4.1.32:

> `YYYY` is the year in the proleptic Gregorian calendar as four decimal digits from 0000 to 9999, or as an expanded year of *"+"* or *"-"* followed by six decimal digits.

## Problem

§21.4.1.32 defines the *input/interchange* grammar accepted by `Date.parse`, where `+002026-01-01T00:00:00.000Z` is a
valid expanded-year representation of 2026 (only `-000000` is forbidden). `Date.prototype.toISOString` step 7 asks for
*"a String representation of _tv_ in the Date Time String Format"* without restricting expanded years to `< 0` or
`> 9999`, leaving `"+002026-01-01T00:00:00.000Z"` a literally conforming result for `new Date(Date.UTC(2026, 0, 1)).toISOString()`.

## Examples

```js
print(new Date(Date.UTC(0, 0, 1)).toISOString());
print(new Date(Date.UTC(2026, 0, 1)).toISOString());
print(new Date(Date.UTC(10000, 0, 1)).toISOString());
```

| | year `1900` (`Date.UTC(0, 0, 1)`) | year `2026` | year `10000` |
|---|---|---|---|
| literal text | `"1900-..."` or `"+001900-..."` | `"2026-..."` or `"+002026-..."` | `"+010000-01-01T00:00:00.000Z"` |
| V8, SpiderMonkey, JavaScriptCore | `"1900-01-01T00:00:00.000Z"` | `"2026-01-01T00:00:00.000Z"` | `"+010000-01-01T00:00:00.000Z"` |
| formal model (test262 reading) | `"1900-01-01T00:00:00.000Z"` | `"2026-01-01T00:00:00.000Z"` | `"+010000-01-01T00:00:00.000Z"` |

## Proposed wording

Add to `Date.prototype.toISOString` step 7: *"representing the year as four digits if 0 ≤ YearFromTime(_tv_) ≤ 9999 and
as an expanded year otherwise."*

## test262

`built-ins/Date/prototype/toISOString/15.9.5.43-0-4.js` and `15.9.1.15-1.js` require exact 4-digit `YYYY` strings for
years in `0..9999`.
