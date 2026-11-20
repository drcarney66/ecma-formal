module

public import Engine.Model.Bare

@[expose] public section

/-!
# Number::toString's digits

`digits b r`: for a finite positive binary64 value `b` and a radix 2 ≤ r ≤ 36, integers n, k and s such that
k ≥ 1, r^(k-1) ≤ s < r^k, the binary64 rounding of s × r^(n-k) is `b`, and k is as small as possible
(sec-numeric-types-number-tostring step 5). With X = ℝ(b) and e the integer with r^(e-1) ≤ X < r^e (`expOf`), it
tries k = 1, 2, …: at each k the six tuples with n from e - 1 to e + 1 and s the floor of X × r^(k-n), clamped to
the k-digit integers, or the next integer, clamped (`tries`); the first k at which one of them meets the condition
is the answer, and of those that meet it the one with s × r^(n-k) closest to X, the even s on a tie (the step's NOTE
recommends it).
-/

namespace Engine.Model.Digits

open Engine.Binary64

/-- The largest j with r^j ≤ n, for 1 ≤ n ≤ the fuel and r ≥ 2. -/
def nlog (r : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n < r then 0 else nlog r f (n / r) + 1

/-- The integer e with r^(e-1) ≤ X < r^e, for X > 0 and r ≥ 2. -/
def expOf (r : Nat) (X : Rat) : Int :=
  if 1 ≤ X then (nlog r X.floor.toNat X.floor.toNat : Int) + 1
  else -(nlog r (X⁻¹.ceil - 1).toNat (X⁻¹.ceil - 1).toNat : Int)

/-- The result of clamping v between lo and hi. -/
def clamp (v lo hi : Int) : Int := if v < lo then lo else if hi < v then hi else v

/-- Whether n, k and s meet the step's condition for b at radix r: r^(k-1) ≤ s < r^k and the rounding of
s × r^(n-k) is b. -/
def meets (b : BitVec 64) (r : Nat) (n : Int) (k : Nat) (s : Int) : Bool :=
  decide ((r : Int) ^ (k - 1) ≤ s) && decide (s < (r : Int) ^ k) && ofRat ((s : Rat) * (r : Rat) ^ (n - k)) == b

/-- The tuples tried at k: n from e - 1 to e + 1, with s the floor of X × r^(k-n), clamped, and the next integer,
clamped. -/
def tries (r : Nat) (X : Rat) (e : Int) (k : Nat) : List (Int × Int) :=
  [e - 1, e, e + 1].flatMap fun n =>
    let f := (X * (r : Rat) ^ ((k : Int) - n)).floor
    [(n, clamp f ((r : Int) ^ (k - 1)) ((r : Int) ^ k - 1)), (n, clamp (f + 1) ((r : Int) ^ (k - 1)) ((r : Int) ^ k - 1))]

/-- |s × r^(n-k) - X| for the tuple (n, s) at k. -/
def dist (r : Nat) (X : Rat) (k : Nat) (t : Int × Int) : Rat :=
  let v := (t.2 : Rat) * (r : Rat) ^ (t.1 - k) - X
  if v < 0 then -v else v

/-- Whether (n, s) is closer to X than (n', s') at k: s × r^(n-k) nearer, or as near with s even. -/
def better (r : Nat) (X : Rat) (k : Nat) (a b : Int × Int) : Bool :=
  dist r X k a < dist r X k b || (dist r X k a == dist r X k b && a.2 % 2 == 0)

/-- The tuple of `ts` closest to X. -/
def best (r : Nat) (X : Rat) (k : Nat) : List (Int × Int) → Option (Int × Int)
  | [] => none
  | t :: ts => some (ts.foldl (fun a c => if better r X k c a then c else a) t)

/-- The tuple taken at k: the closest of the tuples tried that meet the condition, if one does. -/
def at? (b : BitVec 64) (r : Nat) (X : Rat) (e : Int) (k : Nat) : Option (Int × Int) :=
  best r X k ((tries r X e k).filter fun t => meets b r t.1 k t.2)

/-- k, k + 1, …, the fuel's number of them: the first at which a tuple is taken. -/
def search (b : BitVec 64) (r : Nat) (X : Rat) (e : Int) : Nat → Nat → Option (Int × Nat × Int)
  | 0, _ => none
  | f + 1, k => match at? b r X e k with
    | some (n, s) => some (n, k, s)
    | none => search b r X e f (k + 1)

/-- The rounds `search` takes at most: past the k at which a tuple certainly meets the condition. -/
def fuel : Nat := 2200

/-- n, k and s for b at radix r. -/
def digits (b : BitVec 64) (r : Nat) : Int × Nat × Int :=
  let X := toRat b
  (search b r X (expOf r X) fuel 1).getD (0, 0, 0)

/-! ## The place of the first significant digit -/

/-- Whether 10^e ≤ X < 10^(e+1). -/
def isDecExp (X : Rat) (e : Int) : Bool := decide (((10 : Nat) : Rat) ^ e ≤ X) && decide (X < ((10 : Nat) : Rat) ^ (e + 1))

/-- The integer e with 10^e ≤ X < 10^(e+1), for X > 0: estimated from the bit lengths of X's numerator and
denominator (log₁₀ 2 ≈ 0.30103), the estimate and its neighbours checked, `expOf` where none is it. -/
def decExp (X : Rat) : Int :=
  let est : Int := ((Nat.log2 X.num.natAbs : Int) - (Nat.log2 X.den : Int)) * 30103 / 100000
  match [est, est - 1, est + 1, est - 2, est + 2].find? (isDecExp X) with
  | some e => e
  | none => expOf 10 X - 1

end Engine.Model.Digits
