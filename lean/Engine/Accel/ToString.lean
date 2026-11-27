module

public import Ecma.State
public import Ecma.Prims.Strings
public import Engine.Model

@[expose] public section

/-!
# Number::toString at Impl

The result String for a Number and a radix (an integer from 2 to 36): step 5's n, k and s the model's
(`numDigits`, as the reading's primitives answer), its other steps and the overlay algorithms their phrases name in
the machine's operations (`render?`), x < -0 as the machine compares Numbers. It declines where a loop would take
more rounds than its bound (`kRounds`, `occRounds`), an Assert would fail, or step 3's call on -x would call again.
-/

namespace Engine.Accel

open Ecma Engine.Model

abbrev F := Engine.Impl

/-- An entry's run that never declines. -/
def always (m : Run F (Val F)) : Run F (Option (Val F)) := fun s => Run.Res.bind (m s) fun v t => .ok (some v) t

def int? : MathVal → Option Int
  | .int i => some i
  | _ => none

/-! ## Number::toString -/

/-! ### The machine's operations on mathematical values

Each `none` where the machine stops: `binOp`, `relOp`, ⌊⌋. -/

/-- x o y (`binOp`). -/
def op? (o : BinOp) (x y : F.Math) : Option F.Math := mathOp (M := F) o x y

/-- x < y (`relOp`). -/
def lt? (x y : F.Math) : Option Bool := some (F.lt x y)

/-- x = y (`relOp`). -/
def eq? (x y : F.Math) : Option Bool := some (F.eq x y)

/-- x ≤ y (`relOp`). -/
def le? (x y : F.Math) : Option Bool := do return (← lt? x y) || (← eq? x y)

/-- floor(x). -/
def floor? (x : F.Math) : Option F.Math := some (F.floor x)

def one : F.Math := F.ofNat 1

/-- Step 5 for a finite x > +0𝔽 at radix r: n, k and s, as NumberDigitsExponent, NumberDigitsCount and
NumberDigitsSignificand answer. -/
def step5 (r : F.Math) (xb : F.Num) : F.Math × F.Math × F.Math :=
  let d := F.numDigits xb r
  (d.1, F.ofNat d.2.1, d.2.2)

/-- Whether the primitives answer at x with ℝ(x) = m and radix r: m > 0 and r an integer from 2 to 36. -/
def step5Ok (r m : F.Math) : Bool := F.lt (F.ofNat 0) m && F.isInt r && !F.lt r (F.ofNat 2) && !F.lt (F.ofNat 36) r

/-! ### Steps 6 to 11 in the machine's operations

Each overlay algorithm the steps' phrases name, its Asserts as guards, on Strings of code units. -/

/-- x ≥ y (`relOp`). -/
def ge? (x y : F.Math) : Option Bool := do return (← lt? y x) || (← eq? x y)

/-- x ≠ y (`relOp`). -/
def ne? (x y : F.Math) : Option Bool := do return !(← eq? x y)

/-- `a or b`, b only when a is false. -/
def or? : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | some false, b => b
  | none, _ => none

/-- lo ≤ n ≤ hi on mathematical values (`inInterval`). -/
def inInt? (lo hi n : F.Math) : Option Bool := do return (← le? lo n) && (← le? n hi)

/-- abs(x). -/
def abs (x : F.Math) : F.Math := if F.lt x (F.ofNat 0) then F.neg x else x

/-- The String of code units and Strings (`strOfUnits`). -/
def cat? (vs : List (Val F)) : Option F.Str :=
  vs.foldl (fun acc v => match acc, v with
    | some t, .math u => if Prims.Strings.isUnit (M := F) u then some (F.strConcat t (F.strOfUnit u)) else none
    | some t, .str u => some (F.strConcat t u)
    | _, _ => none) (some (F.strLit ""))

/-- The substring of t from i to j (`subOf`). -/
def sub? (t : F.Str) (i j : F.Math) : Option F.Str :=
  if !(F.isInt i && F.isInt j) then none
  else if F.lt i (F.ofNat 0) || F.lt j i || F.lt (F.strLen t) j then none
  else some (F.strSub t i j)

/-- The representation of n using radix r. -/
def repr? (n r : F.Math) : Option F.Str := do
  guard (F.isInt n && F.isInt r)
  guard (← ge? n (F.ofNat 0))
  guard (← inInt? (F.ofNat 2) (F.ofNat 36) r)
  return F.intToRadix n r

/-- The decimal representation of n. -/
def dec? (n : F.Math) : Option F.Str := repr? n (F.ofNat 10)

/-- The single digit of n. -/
def single? (n : F.Math) : Option F.Str := do
  guard (← lt? n (F.ofNat 10))
  dec? n

/-- The most significant digit of s. -/
def msd? (s : F.Str) : Option F.Str := do
  guard !(F.strEq s (F.strLit ""))
  sub? s (F.ofNat 0) (F.ofNat 1)

/-- The k digits of s. -/
def kDigits? (k : F.Math) (s : F.Str) : Option F.Str := do
  guard (F.eq (F.strLen s) k)
  return s

/-- The most significant k digits of s. -/
def msk? (k : F.Math) (s : F.Str) : Option F.Str := do
  guard (← le? k (F.strLen s))
  sub? s (F.ofNat 0) k

/-- The remaining k digits of s. -/
def rem? (k : F.Math) (s : F.Str) : Option F.Str := do
  guard (← le? k (F.strLen s))
  sub? s (← op? .sub (F.strLen s) k) (F.strLen s)

/-- The code unit of s. -/
def cu? (s : F.Str) : Option F.Math := do
  guard (F.eq (F.strLen s) (F.ofNat 1))
  F.strAt s (F.ofNat 0)

/-- n occurrences of c. -/
def occ? (n c : F.Math) : Option F.Str := do
  guard (F.isInt n && !F.lt n (F.ofNat 0))
  return F.strRepeat n (← cat? [.math c])

/-- Steps 6 to 11 from step 5's n, k and s at radix r. -/
def render? (r n k s : F.Math) : Option F.Str := do
  if ← or? (ne? r (F.ofNat 10)) (inInt? (.int (-5)) (F.ofNat 21) n) then
    if ← ge? n k then
      cat? [.str (← kDigits? k (← repr? s r)), .str (← occ? (← op? .sub n k) (F.ofNat 48))]
    else if ← lt? (F.ofNat 0) n then
      cat? [.str (← msk? n (← repr? s r)), .math (F.ofNat 46), .str (← rem? (← op? .sub k n) (← repr? s r))]
    else
      guard (← le? n (F.ofNat 0))
      cat? [.math (F.ofNat 48), .math (F.ofNat 46), .str (← occ? (F.neg n) (F.ofNat 48)),
        .str (← kDigits? k (← repr? s r))]
  else
    guard (F.eq r (F.ofNat 10))
    let sign : F.Math := if ← lt? n (F.ofNat 0) then F.ofNat 45 else F.ofNat 43
    let ex ← dec? (abs (← op? .sub n one))
    if ← eq? k one then
      cat? [.math (← cu? (← single? s)), .math (F.ofNat 101), .math sign, .str ex]
    else
      cat? [.math (← cu? (← msd? (← dec? s))), .math (F.ofNat 46), .str (← rem? (← op? .sub k one) (← dec? s)),
        .math (F.ofNat 101), .math sign, .str ex]

/-- Steps 4 to 11, for x not NaN, not zero and not below -0. -/
def fromStep4 (r : F.Math) (x : F.Num) : Option F.Str :=
  match F.numView x with
  | .posInf => some (F.strLit "Infinity")
  | .finite m => if step5Ok r m then render? r (step5 r x).1 (step5 r x).2.1 (step5 r x).2.2 else none
  | _ => none

/-- Steps 1 to 11 of Number::toString(x, r), `neg` step 3's call on -x. -/
def fromStep1 (r : F.Math) (neg : F.Num → Option F.Str) (x : F.Num) : Option F.Str :=
  match F.numView x with
  | .nan => some (F.strLit "NaN")
  | .posZero | .negZero => some (F.strLit "0")
  | _ => if F.numLt x (F.numZero true) then do
      cat? [.str (F.strLit "-"), .str (← neg (F.numNeg x))]
    else fromStep4 r x

/-- Number::toString(x, r): step 3's call on -x declines where it would call again. -/
def numberToStr (r : F.Math) (x : F.Num) : Option F.Str :=
  fromStep1 r (fromStep1 r fun _ => none) x

/-- Number::toString(x, r) as a String. -/
def numberToString (r : Nat) (x : F.Num) : Option String :=
  (numberToStr (F.ofNat r) x).map fun t => String.ofList (t.toList.map fun u => Char.ofNat u.toNat)

/-- Non-negative safe integer `0 ≤ n < 2^53` whose canonical binary64 Number is `x`, if any. -/
def safeNatOf? (x : F.Num) : Option Nat :=
  if x == F.numZero false then some 0
  else match F.numView x with
    | .finite (.int i) =>
      if 0 < i && i < 2 ^ 53 then
        let n := i.toNat
        if x == F.numOf (.int n) then some n else none
      else none
    | _ => none

/-- Decimal string of `n : Nat` (`"0"` at `0`, `toString n` at `n > 0`). -/
def natDecStr (n : Nat) : String :=
  if n == 0 then "0" else toString n

/-- `Number::toString(x, 10)` on canonical non-negative safe integers `< 2^53`. -/
def numToStrEntry : List (Val F) → Option (Run F (Option (Val F)))
  | [.num x, .math (.int 10)] =>
    (safeNatOf? x).map fun n => always (pure (.str (F.strLit (natDecStr n))))
  | _ => none

/-- `ToString(argument)` on Strings and canonical non-negative safe integer Numbers `< 2^53`. -/
def toStrEntry : List (Val F) → Option (Run F (Option (Val F)))
  | [.str t] =>
    some (always (pure (.comp Known.eNormal (.str t) (.enum Known.eEmpty))))
  | [.num x] =>
    (safeNatOf? x).map fun n =>
      always (pure (.comp Known.eNormal (.str (F.strLit (natDecStr n))) (.enum Known.eEmpty)))
  | _ => none

end Engine.Accel
