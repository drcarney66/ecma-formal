# 10. `new Date(0).setHours(1e21)`: UTC ( _t_ ) reaches a failing Assert

- **Location:** §21.4.1.18 GetUTCEpochNanoseconds (`#sec-getutcepochnanoseconds`), step 4, reached from §21.4.1.26
  UTC ( _t_ ) (`#sec-utc-t`), step 4.a, through §21.4.1.20 GetNamedTimeZoneEpochNanoseconds
  (`#sec-getnamedtimezoneepochnanoseconds`), step 2; §21.4.1.28 MakeDay (`#sec-makeday`), step 8.
- **Kind:** failing Assert, MakeDay's ambiguous "finite time value", and `epoch nanoseconds count` return-range overflow.
- **Model errata:** `GetUTCEpochNanosecondsNaN` (baked-in SpecTec reading: literal, stopping at `GetUTCEpochNanoseconds`
  step 4) and `MakeDayFiniteTimeValue` (baked-in SpecTec reading: proposed in `spec/spectec/clauses/S21.spectec` and
  `@sort-time-value`, reading MakeDay step 8's "finite time value" as any finite integral Number rather than restricting
  to ±8.64 × 10<sup>15</sup> ms; additionally, return-sort checking is omitted at runtime so `GetUTCEpochNanoseconds`
  exceeding `MinEpochNanoseconds..MaxEpochNanoseconds` on large `UTC(_t_)` inputs does not stop).
- **Upstream:** Checked 2026-11-19: PR #3464 (open, 2024-10), "Editorial: Add "local-offset time value" for time
  values with local time zone offset applied", has a commit, "Editorial: Handle too large inputs early in UTC"
  (e8051bb98), that adds to UTC the range check proposed here; it is not merged. Related, open: issue #1087 (open,
  2018-02), "MakeDay should be more explicit how unreasonably large numbers are handled"; issue #3992 (open, 2026-10),
  "DayWithinYear AO can return -1 due to floating point errors", on `new Date(2000, 0, 106752348147)`; issue #4086
  (open, 2026-11), "Argument type of UTC and TimeString should be integral Number", which says #3464 addresses the
  range; PR #3995 (open, 2026-10), "Editorial: relax/restrict some Date AO types appropriately", which makes UTC's
  step 1 "If _t_ is *NaN*" and adds no range check.

## Text

UTC ( _t_ ):

> 1. If _t_ is not a finite Number, return *NaN*.
> …
> 4. Else,
>    a. Let _possibleInstants_ be GetNamedTimeZoneEpochNanoseconds(_systemTimeZoneIdentifier_, YearFromTime(_t_),
>       MonthFromTime(_t_) + 1, DateFromTime(_t_), HourFromTime(_t_), MinuteFromTime(_t_), SecondFromTime(_t_),
>       MillisecondFromTime(_t_), 0, 0).
>
> Input _t_ is nominally a time value but may be any Number value. The algorithm must not limit _t_ to the time
> value range, so that inputs corresponding with a boundary of the time value range can be supported regardless of
> local UTC offset.

GetUTCEpochNanoseconds (which the default GetNamedTimeZoneEpochNanoseconds calls for *"UTC"*):

> 1. Let _date_ be MakeDay(𝔽(_year_), 𝔽(_month_ - 1), 𝔽(_day_)).
> 2. Let _time_ be MakeTime(𝔽(_hour_), 𝔽(_minute_), 𝔽(_second_), 𝔽(_millisecond_)).
> 3. Let _epochMilliseconds_ be MakeDate(_date_, _time_).
> 4. Assert: _epochMilliseconds_ is an integral Number.

MakeDay:

> 8. Find a finite time value _tv_ such that YearFromTime(_tv_) = ℝ(_balancedYear_), MonthFromTime(_tv_) =
>    _balancedMonthMV_, and DateFromTime(_tv_) = 1; but if this is not possible (because some argument is out of
>    range), return *NaN*.

## Problem

The local-time paths (the Date constructor with several arguments, `setHours`, `setMinutes`, `setSeconds`,
`setMilliseconds`, `setDate`, `setMonth`, `setFullYear`) compute a local time with MakeTime and MakeDate and pass it
to UTC before TimeClip. MakeTime does not bound its result: `new Date(0).setHours(1e21)` (in UTC) gives _t_ =
1e21 × 3.6 × 10⁶ = 3.6 × 10²⁷, which is finite, so step 1 does not return. Its date is 9 January of the year
114079458624523116 (≈ 1.1 × 10¹⁷). GetUTCEpochNanoseconds step 1 asks MakeDay for a finite time value on 1 January
of that year, and there is none: adjacent Numbers there are 2³⁹ ms (about 17 years) apart, and the only one in that
January is _t_ itself, on the 9th. So MakeDay returns *NaN*, MakeDate is *NaN*, and the Assert of step 4 is false.
The intended result is the one TimeClip would give: *NaN*.

**A question on MakeDay step 8.** §21.4.1.1 says both that a finite time value is "an integral Number representing an
instant in time to millisecond precision" and that "A time value supports a slightly smaller range of
-8,640,000,000,000,000 to 8,640,000,000,000,000 milliseconds". If step 8's "finite time value" were limited to that
range, the step's result would differ when the month's first day is outside the range but the requested day inside it
(step 9 adds the day afterwards): `Date.UTC(275761, 0, -256)` would be *NaN* rather than 8639987299200000 (19 April
275760). And the Assert above would fail even with the step proposed below: `new Date(-8.64e15).setHours(-1)` (in UTC)
is 19 April -271821, and 1 April -271821 is outside the range. The first of these sentences defines a finite time
value as any integral Number, which settles step 8 as the engines read it. Is that the intent, so that the range
sentence does not limit step 8? If so, a note in MakeDay would say so.

## Examples

[examples/10-utc-large-local-time.js](examples/10-utc-large-local-time.js) (outputs:
[RESULTS.md](examples/RESULTS.md#10-utc-large-local-timejs)):

```js
print(Date.UTC(275761, 0, -256));            // range reading: NaN; any-integral reading: 8639987299200000
print(Date.UTC(275760, 8, 13));              // the last time value, either reading
print(new Date(0).setUTCHours(1e21));        // the UTC setter: no UTC(t), NaN
print(new Date(0).setHours(1e21));           // local: UTC(t) with t = 3.6e27
print(new Date(2000, 0, 1, 1e21).getTime()); // the constructor: UTC(t)
```

| | `Date.UTC(275761, 0, -256)` | `Date.UTC(275760, 8, 13)` | `setUTCHours` | `setHours` | constructor |
|---|---|---|---|---|---|
| literal text, any integral Number | 8639987299200000 | 8640000000000000 | *NaN* | Assert fails | Assert fails |
| literal text, the range | *NaN* | 8640000000000000 | *NaN* | Assert fails | Assert fails |
| V8, SpiderMonkey, JavaScriptCore | `8639987299200000` | `8640000000000000` | `NaN` | `NaN` | `NaN` |
| formal model (literal reading) | (not printed) | (not printed) | (not printed) | stops at step 4's Assert | (not reached) |

SpecTec bakes in reading MakeDay step 8 as any finite integral Number (`MakeDayFiniteTimeValue`, `spec/spectec/clauses/S21.spectec`).
For `UTC`, SpecTec keeps the literal wording (`GetUTCEpochNanosecondsNaN`), so its run stops at `GetUTCEpochNanoseconds`
step 4 (`stop: assertFailed sec-getutcepochnanoseconds#0 4`); under the proposed `UTC` guard it prints the engines' five lines.

## Proposed wording

Proposed: a range check after step 1 (MillisecondsPerDay is a mathematical value). Every caller of UTC applies
TimeClip, and a local offset is less than a day, so the result is the one TimeClip gives:

```diff
--- a/spec.html
+++ b/spec.html
@@ -34292,6 +34292,7 @@
         </dl>
         <emu-alg>
           1. If _t_ is not a finite Number, return *NaN*.
+          1. If abs(ℝ(_t_)) ≥ 8.64 × 10<sup>15</sup> + MillisecondsPerDay, return *NaN*.
           1. Let _systemTimeZoneIdentifier_ be SystemTimeZoneIdentifier().
           1. If IsTimeZoneOffsetString(_systemTimeZoneIdentifier_) is *true*, then
             1. Let _offsetNanoseconds_ be ParseTimeZoneOffsetString(_systemTimeZoneIdentifier_).
```

The model's proposed reading returns *NaN* at the same place when MakeDay(𝔽(YearFromTime(_t_)),
𝔽(MonthFromTime(_t_)), *1*𝔽) is *NaN*, exactly when step 4.a would fail; after TimeClip the two give the same
results.

## test262

The `built-ins/Date/prototype/*/new-value-time-clip.js` tests keep the first day of the month inside the range.
`built-ins/Date/makedate-float-arithmetic.js` passes UTC a local time far past it (`new Date(2000, 0,
106752348147)`, about 9.2 × 10¹⁸ ms) and requires *NaN*, but Numbers there are 2048 ms apart, so MakeDay finds the
month's first day and the Assert holds (the model prints `NaN`). No test reaches the Assert or decides MakeDay step 8.
