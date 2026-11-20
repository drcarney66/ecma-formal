module

public import Ecma.Model

@[expose] public section

/-!
# Calendar epoch helpers (§21.4.1)

Time-value range (`maxTime`, `inTime`) and the calendar epoch calculation (`leapDays`, `daysBefore`,
`yearDay`, `dateMs`) used by the host date laws (`Ecma.Host.Laws.DateFormat`).
-/

namespace Ecma

/-- The code units of an ASCII string. -/
def textUnits (s : String) : List Nat := s.toList.map Char.toNat

/-- An integer as a model mathematical value. -/
def intMath {M : Model} : Int → M.Math
  | .ofNat n => M.ofNat n
  | .negSucc n => M.neg (M.ofNat (n + 1))

/-- The time value limit, 8.64 × 10^15 milliseconds (§21.4.1.1). -/
def maxTime : Nat := 8640000000000000

/-- Whether `t` is within ECMAScript's time value range (`|t| ≤ 8.64 × 10^15`). -/
def inTime (t : Int) : Bool := decide (t.natAbs ≤ maxTime)

/-- Whether year `y` is a leap year (1 or 0 extra days, §21.4.1.3). -/
def leapDays (y : Int) : Nat := if y % 4 ≠ 0 then 0 else if y % 100 ≠ 0 then 1 else if y % 400 ≠ 0 then 0 else 1

/-- Days in year `y` before 1-based month `mo` (1..12). -/
def daysBefore (y : Int) (mo : Nat) : Nat :=
  ([0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334].getD (mo - 1) 0) + if 2 < mo then leapDays y else 0

/-- DayFromYear(y) (§21.4.1.3). -/
def yearDay (y : Int) : Int := 365 * (y - 1970) + (y - 1969) / 4 - (y - 1901) / 100 + (y - 1601) / 400

/-- Time value in milliseconds from year, 1-based month, day, hour, minute, second and millisecond. -/
def dateMs (y : Int) (mo d h mi sc ms : Nat) : Int :=
  (yearDay y + daysBefore y mo + ((d : Int) - 1)) * 86400000 + (((h * 60 + mi) * 60 + sc) * 1000 + ms : Nat)

end Ecma
