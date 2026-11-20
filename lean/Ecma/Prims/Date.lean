module

public import Ecma.State

@[expose] public section

/-!
# Date primitives: YearFromTime's year and MakeDay's first day

The two choices of §21.4.1 as functions: YearFromTimeOf(tv), the largest integer y with
TimeFromYear(y) ≤ tv (§21.4.1.7), found next to the year of the mean Gregorian year, and FirstDayOf(y, m), the least time value whose YearFromTime is
y, MonthFromTime m and DateFromTime 1, or NaN where there is none (§21.4.1.28 step 8). The integer
search is an exponential search from 0 for a bracket, then bisection, over integers of magnitude at
most 2^1099 (beyond every finite Number); undecided where the predicate is.
-/

namespace Ecma.Prims.Date

variable {M : Model}

/-! ## The integer search -/

/-- The search's steps: 2^(bound - 1) exceeds every finite Number value. -/
def bound : Nat := 1100

/-- 2^k. -/
def pow2 (k : Nat) : M.Math := M.ofNat (2 ^ k)

/-- One half. -/
def half : M.Math := M.div (M.ofNat 1) (M.ofNat 2)

/-- The largest integer in [lo, hi) p holds of, given p lo and not p hi: bisection. -/
def bisect (p : M.Math → Option Bool) : Nat → M.Math → M.Math → Option M.Math
  | 0, _, _ => none
  | f + 1, lo, hi =>
    if !M.lt (M.add lo (M.ofNat 1)) hi then some lo
    else
      let mid := M.floor (M.div (M.add lo hi) (M.ofNat 2))
      match p mid with
      | some true => bisect p f mid hi
      | some false => bisect p f lo mid
      | none => none

/-- From `lo`, which p holds of, up through 2^k, 2^(k+1), … to the first p fails at; then bisected. -/
def up (p : M.Math → Option Bool) : Nat → Nat → M.Math → Option M.Math
  | 0, _, _ => none
  | f + 1, k, lo =>
    let x := pow2 (M := M) k
    match p x with
    | some true => up p f (k + 1) x
    | some false => bisect p (2 * bound + 4) lo x
    | none => none

/-- From `hi`, which p fails at, down through -2^k, -2^(k+1), … to the first p holds of; then bisected. -/
def down (p : M.Math → Option Bool) : Nat → Nat → M.Math → Option M.Math
  | 0, _, _ => none
  | f + 1, k, hi =>
    let x := M.neg (pow2 (M := M) k)
    match p x with
    | some true => bisect p (2 * bound + 4) x hi
    | some false => down p f (k + 1) x
    | none => none

/-- The largest integer p holds of, checked: p r, not p (r + 1), not p (r + ½). -/
def largest (p : M.Math → Option Bool) : Option M.Math := do
  let r ← match p (M.ofNat 0) with
    | some true => up p bound 0 (M.ofNat 0)
    | some false => down p bound 0 (M.ofNat 0)
    | none => none
  match p r, p (M.add r (M.ofNat 1)), p (M.add r half) with
  | some true, some false, some false => some r
  | _, _, _ => none

/-- The smallest integer p holds of: the negation of the largest of x ↦ p (-x). -/
def smallest (p : M.Math → Option Bool) : Option M.Math :=
  (largest fun x => p (M.neg x)).map M.neg

/-! ## The date arithmetic -/

/-- msPerDay (§21.4.1.1). -/
def msPerDay : M.Math := M.ofNat 86400000

/-- DayFromYear(y) (§21.4.1.5). -/
def dayFromYear (y : M.Math) : M.Math :=
  let q (a b : Nat) := M.floor (M.div (M.sub y (M.ofNat a)) (M.ofNat b))
  M.add (M.sub (M.add (M.mul (M.ofNat 365) (M.sub y (M.ofNat 1970))) (q 1969 4)) (q 1901 100)) (q 1601 400)

/-- 𝔽(x): +0𝔽 for 0. -/
def numFor (x : M.Math) : Option M.Num :=
  some (if M.eq x (M.ofNat 0) then M.numZero false else M.numOf x)

/-- TimeFromYear(y) (§21.4.1.6): 𝔽(msPerDay × DayFromYear(y)). -/
def timeFromYear (y : M.Math) : Option M.Num := numFor (M.mul msPerDay (dayFromYear y))

/-- YearFromTime's condition at y: y is an integer and TimeFromYear(y) ≤ tv. -/
def yearLe (tv : M.Num) (y : M.Math) : Option Bool :=
  if !M.isInt y then some false
  else (timeFromYear y).map fun t => M.numLt t tv || M.numEq t tv

/-- MakeDay's _dayWithinYear_ of the first day of month m (0 to 11), after a leap day l. -/
def monthStart (l m : M.Math) : M.Math :=
  let k (a : Nat) := M.ofNat a
  let ml (a : Nat) := M.add (k a) l
  if M.eq m (k 0) then k 0 else if M.eq m (k 1) then k 31 else if M.eq m (k 2) then ml 59
  else if M.eq m (k 3) then ml 90 else if M.eq m (k 4) then ml 120 else if M.eq m (k 5) then ml 151
  else if M.eq m (k 6) then ml 181 else if M.eq m (k 7) then ml 212 else if M.eq m (k 8) then ml 243
  else if M.eq m (k 9) then ml 273 else if M.eq m (k 10) then ml 304 else ml 334

/-- A month number: an integer from 0 to 11. -/
def isMonth (m : M.Math) : Bool := M.isInt m && !M.lt m (M.ofNat 0) && M.lt m (M.ofNat 12)

/-- The least ℝ(t) of the Numbers t ≥ the Number b with ℝ(t) ≥ lo; `none` for b = +∞ (or NaN). -/
def lower (b : M.Num) (lo : M.Math) : Option M.Math := match M.numView b with
  | .finite x => some (if M.lt lo x then x else lo)
  | .posZero | .negZero => some (if M.lt lo (M.ofNat 0) then M.ofNat 0 else lo)
  | .negInf => some lo
  | _ => none

/-- The bound min(ℝ(b), hi) of the Numbers t < the Number b with ℝ(t) < hi; `none` for b = -∞ (or NaN). -/
def upper (b : M.Num) (hi : M.Math) : Option M.Math := match M.numView b with
  | .finite x => some (if M.lt x hi then x else hi)
  | .posZero | .negZero => some (if M.lt (M.ofNat 0) hi then M.ofNat 0 else hi)
  | .posInf => some hi
  | _ => none

/-- Whether k is an integer whose 𝔽(k) is at least lo. -/
def atLeast (lo k : M.Math) : Option Bool :=
  if !M.isInt k then some false
  else (numFor k).bind fun n => match M.numView n with
    | .finite x => some !(M.lt x lo)
    | .posZero | .negZero => some !(M.lt (M.ofNat 0) lo)
    | .posInf => some true
    | .negInf => some false
    | .nan => none

/-- The least Number in [max(msPerDay × D, TimeFromYear(y)), min(msPerDay × (D + 1), TimeFromYear(y + 1))), D month m's first day of year y; else NaN. -/
def firstDay (y m : M.Math) : Option M.Num := do
  let d0 := dayFromYear y
  let d := M.add d0 (monthStart (M.sub (M.sub (dayFromYear (M.add y (M.ofNat 1))) d0) (M.ofNat 365)) m)
  let t0 ← timeFromYear y
  let t1 ← timeFromYear (M.add y (M.ofNat 1))
  match lower t0 (M.mul msPerDay d), upper t1 (M.mul msPerDay (M.add d (M.ofNat 1))) with
  | some lo, some hi =>
    let k ← smallest (atLeast lo)
    let t ← numFor k
    match M.numView t with
    | .finite x => return if M.lt x hi then t else M.numNaN
    | .posZero | .negZero => return if M.lt (M.ofNat 0) hi then t else M.numNaN
    | _ => return M.numNaN
  | _, _ => return M.numNaN

/-- The year a time value falls in by the mean Gregorian year (365.2425 days): 1970 + floor(ℝ(tv) / (msPerDay ×
365.2425)), within a year of YearFromTime(tv); `none` for a Number that is not finite. -/
def yearGuess (tv : M.Num) : Option M.Math := match M.numView tv with
  | .finite x => some (M.add (M.ofNat 1970) (M.floor (M.div x (M.mul msPerDay (M.div (M.ofNat 3652425) (M.ofNat 10000))))))
  | .posZero | .negZero => some (M.ofNat 1970)
  | _ => none

/-- From y, the integer r with p r and not p (r + 1), each step one year up or down; `none` after `f` steps. For a p
that holds up to some integer and not above it, r is the largest integer p holds of. -/
def near (p : M.Math → Option Bool) : Nat → M.Math → Option M.Math
  | 0, _ => none
  | f + 1, y => match p y, p (M.add y (M.ofNat 1)) with
    | some true, some false => some y
    | some true, some true => near p f (M.add y (M.ofNat 1))
    | some false, _ => near p f (M.sub y (M.ofNat 1))
    | _, _ => none

/-- YearFromTimeOf(tv) (§21.4.1.7): the largest integer y with TimeFromYear(y) ≤ tv. TimeFromYear is increasing, so
it is the y with TimeFromYear(y) ≤ tv < TimeFromYear(y + 1): found from the mean-year estimate (`yearGuess`) in a
few steps, or by the search where there is none. -/
def yearFromTime : List (Val M) → Run M (Val M)
  | [.num tv] => match ((yearGuess tv).bind (near (yearLe tv) 8)).orElse fun _ => largest (yearLe tv) with
    | some y => Run.pure (.math y)
    | none => Run.stop .residue
  | _ => Run.stop .sortError

/-- FirstDayOf(y, m) (§21.4.1.28 step 8): the first day of month m of year y as a time value, or NaN. -/
def firstDayOf : List (Val M) → Run M (Val M)
  | [.math y, .math m] =>
    if M.isInt y && isMonth m then match firstDay y m with
      | some t => Run.pure (.num t)
      | none => Run.stop .residue
    else Run.stop .sortError
  | _ => Run.stop .sortError

end Ecma.Prims.Date
