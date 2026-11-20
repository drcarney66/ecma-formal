module

public import Ecma.Host.DateParse
public import Engine.Host.Strategy

@[expose] public section

/-!
# The host's date parser (§21.4.3.2)

`dateParse` and `parseDateNum`: ParseDateString's parser for the Date Time String Format,
`toUTCString`, and `toString`, over code units.
-/

namespace Ecma

/-- The Names of the days of the week, by WeekDay Index (sec-todatestring-day-names). -/
def dayNames : List String := ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]

/-- The Names of the months of the year, by Month Index (sec-todatestring-month-names). -/
def monthNames : List String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-! Date.parse over code units: the Date Time String Format (§21.4.1.32), a date-time form without a
UTC offset read as UTC; the Strings of toUTCString and of toString, any UTC offset and time zone
name; any other String is unrecognized. -/

/-- `n` ASCII decimal digits at the front of `cs`: their value and the rest. -/
def dateDigits : Nat → List Nat → Option (Nat × List Nat)
  | 0, cs => some (0, cs)
  | n + 1, c :: cs => if 48 ≤ c ∧ c ≤ 57 then
      (dateDigits n cs).map fun (v, r) => ((c - 48) * 10 ^ n + v, r)
    else none
  | _ + 1, [] => none

/-- The ASCII decimal digits at the front of `cs`: their number, their value and the rest. -/
def dateRun : List Nat → Nat × Nat × List Nat
  | c :: cs => if 48 ≤ c ∧ c ≤ 57 then
      match dateRun cs with
      | (k, v, r) => (k + 1, (c - 48) * 10 ^ k + v, r)
    else (0, 0, c :: cs)
  | [] => (0, 0, [])

/-- The code units `l` at the front of `cs`: the rest. -/
def dateLit : List Nat → List Nat → Option (List Nat)
  | [], cs => some cs
  | a :: l, c :: cs => if a = c then dateLit l cs else none
  | _ :: _, [] => none

/-- The year: four digits, or a sign and six digits other than -000000. -/
def dateYear : List Nat → Option (Int × List Nat)
  | c :: cs => if c = 43 ∨ c = 45 then (dateDigits 6 cs).bind fun (v, r) =>
        if c = 45 ∧ v = 0 then none else some (if c = 45 then -(v : Int) else v, r)
      else (dateDigits 4 (c :: cs)).map fun (v, r) => ((v : Int), r)
  | [] => none

/-- An optional field: `sep` then `n` digits, else `d` and the input as it is. -/
def dateField (sep : Nat) (n d : Nat) : List Nat → Option (Nat × List Nat)
  | c :: cs => if c = sep then dateDigits n cs else some (d, c :: cs)
  | [] => some (d, [])

/-- The UTC offset in minutes at the end of a date-time: none (a local time, read as UTC), `Z`, or
`±HH:mm` with `HH` at most 23. -/
def dateOffset : List Nat → Option Int
  | [] => some 0
  | c :: cs => if c = 90 then (if cs = [] then some 0 else none) else if c = 43 ∨ c = 45 then do
      let (h, r) ← dateDigits 2 cs
      let r ← dateLit [58] r
      let (mi, r) ← dateDigits 2 r
      if r = [] ∧ h ≤ 23 ∧ mi ≤ 59 then some ((if c = 45 then -1 else 1) * ((h * 60 + mi : Nat) : Int))
      else none
    else none

/-- A time part's optional `:ss`, then optional `.sss`: second, millisecond and the rest. -/
def dateSecond : List Nat → Option (Nat × Nat × List Nat)
  | c :: r => if c = 58 then do
      let (sc, r) ← dateDigits 2 r
      let (ms, r) ← dateField 46 3 0 r
      some (sc, ms, r)
    else some (0, 0, c :: r)
  | [] => some (0, 0, [])

/-- A date-time form's time part after its `T`: hour, minute, second, millisecond and UTC offset in
minutes. -/
def dateTimeIso (cs : List Nat) : Option (Nat × Nat × Nat × Nat × Int) := do
  let (h, r) ← dateDigits 2 cs
  let r ← dateLit [58] r
  let (mi, r) ← dateDigits 2 r
  let (sc, ms, r) ← dateSecond r
  let off ← dateOffset r
  return (h, mi, sc, ms, off)

/-- A date form's optional time part: `T` and its fields, else midnight UTC. -/
def dateTimePart : List Nat → Option (Nat × Nat × Nat × Nat × Int)
  | [] => some (0, 0, 0, 0, 0)
  | c :: r => if c = 84 then dateTimeIso r else none

/-- The time value of these fields less `off` minutes: MakeDate of them where each is in its bounds
(a day at most 31). -/
def dateValue (y : Int) (mo d h mi sc ms : Nat) (off : Int) : Option Int :=
  if 1 ≤ mo ∧ mo ≤ 12 ∧ 1 ≤ d ∧ d ≤ 31 ∧ mi ≤ 59 ∧ sc ≤ 59 ∧ (h < 24 ∨ h = 24 ∧ mi = 0 ∧ sc = 0 ∧ ms = 0) then
    some (dateMs y mo d h mi sc ms - off * 60000)
  else none

/-- The time value of a String in the Date Time String Format, if it is one. -/
def dateIso (cs : List Nat) : Option Int := do
  let (y, r) ← dateYear cs
  let (mo, r) ← dateField 45 2 1 r
  let (d, r) ← dateField 45 2 1 r
  let (h, mi, sc, ms, off) ← dateTimePart r
  dateValue y mo d h mi sc ms off

/-- One of the names `ns` at the front of `cs`: its index and the rest. -/
def dateName (ns : List String) : List Nat → Option (Nat × List Nat)
  | a :: b :: c :: r =>
    let i := (ns.map textUnits).idxOf [a, b, c]
    if i < ns.length then some (i, r) else none
  | _ => none

/-- A year of DateString or toUTCString: an optional *"-"*, then four or more digits. -/
def dateYearRun : List Nat → Option (Int × List Nat)
  | c :: cs => if c = 45 then
      (match dateRun cs with
        | (k, v, r) => if 4 ≤ k then some (-(v : Int), r) else none)
    else match dateRun (c :: cs) with
      | (k, v, r) => if 4 ≤ k then some ((v : Int), r) else none
  | [] => none

/-- TimeString: `HH:mm:ss` and *" GMT"*. -/
def dateClock (cs : List Nat) : Option (Nat × Nat × Nat × List Nat) := do
  let (h, r) ← dateDigits 2 cs
  let r ← dateLit [58] r
  let (mi, r) ← dateDigits 2 r
  let r ← dateLit [58] r
  let (sc, r) ← dateDigits 2 r
  let r ← dateLit (textUnits " GMT") r
  return (h, mi, sc, r)

/-- toUTCString's String after `Www,`: ` DD Mmm YYYY HH:mm:ss GMT`. -/
def dateUTCRest (r : List Nat) : Option Int := do
  let r ← dateLit [32] r
  let (d, r) ← dateDigits 2 r
  let r ← dateLit [32] r
  let (mo, r) ← dateName monthNames r
  let r ← dateLit [32] r
  let (y, r) ← dateYearRun r
  let r ← dateLit [32] r
  let (h, mi, sc, r) ← dateClock r
  if r = [] then dateValue y (mo + 1) d h mi sc 0 0 else none

/-- TimeZoneString's offset `±hhmm` in minutes, then nothing or ` (` … `)`. -/
def dateZone : List Nat → Option Int
  | c :: r => if c = 43 ∨ c = 45 then do
      let (oh, r) ← dateDigits 2 r
      let (om, r) ← dateDigits 2 r
      if r = [] ∨ r.take 2 = [32, 40] ∧ r.getLast? = some 41 then
        some ((if c = 45 then -1 else 1) * ((oh * 60 + om : Nat) : Int))
      else none
    else none
  | [] => none

/-- toString's String after `Www `: `Mmm DD YYYY HH:mm:ss GMT±hhmm`, then nothing or ` (` … `)`. -/
def dateLocalRest (r : List Nat) : Option Int := do
  let (mo, r) ← dateName monthNames r
  let r ← dateLit [32] r
  let (d, r) ← dateDigits 2 r
  let r ← dateLit [32] r
  let (y, r) ← dateYearRun r
  let r ← dateLit [32] r
  let (h, mi, sc, r) ← dateClock r
  let off ← dateZone r
  dateValue y (mo + 1) d h mi sc 0 off

/-- A String of toUTCString's or toString's form after the week day name. -/
def dateTextRest : List Nat → Option Int
  | c :: r => if c = 44 then dateUTCRest r else if c = 32 then dateLocalRest r else none
  | [] => none

/-- The time value of a String in the Date Time String Format or of toUTCString's or toString's
form: by its first code unit, a letter for the latter. -/
def dateParse (cs : List Nat) : Option Int :=
  if cs.head?.any (65 ≤ ·) then (dateName dayNames cs).bind fun (_, r) => dateTextRest r else dateIso cs

/-- `n` is the integral Number `t` (`numIs`) and a time value (`instantB`), decided. -/
def dateNumB {M : Model} (n : M.Num) (t : Int) : Bool :=
  instantB n && match M.numView n with
    | .posZero => t == 0
    | .finite m => t != 0 && M.eq m (intMath t)
    | _ => false

/-- ParseDateString's Number for the code units `cs`: `dateParse`'s time value where it is in
range, else *NaN*; none where the model's Number of it is not it (`dateNumB`). -/
def parseDateNum {M : Model} (cs : List Nat) : Option M.Num :=
  match dateParse cs with
  | some t => if inTime t then
      if dateNumB (M.numOf (intMath t)) t then some (M.numOf (intMath t)) else none
    else some M.numNaN
  | none => some M.numNaN

end Ecma
