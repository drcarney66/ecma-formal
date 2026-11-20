module

public import Engine.Model.Binary64

@[expose] public section

/-!
# Real powers of positive rationals

`b^e` for rationals `b > 0` and `e`: exact where it is rational; otherwise enclosed by
`exp(e·ln b)` (ln by the atanh series, exp by Taylor's series after reduction by ln 2) with
dyadic ends rounded outward, refined until both ends round to the same binary64 value. An
irrational value is neither a binary64 value nor a tie, so the refinement ends.
-/

namespace Engine.RPow

/-- `x` rounded down to a multiple of 2^-p. -/
def dn (p : Nat) (x : Rat) : Rat := mkRat (x * ((2 ^ p : Nat) : Rat)).floor (2 ^ p)

/-- `x` rounded up to a multiple of 2^-p. -/
def up (p : Nat) (x : Rat) : Rat := mkRat (x * ((2 ^ p : Nat) : Rat)).ceil (2 ^ p)

/-- The guard bits for `p`. -/
def guard (p : Nat) : Nat := p + 8 + Nat.log2 (p + 1)

/-- An enclosure of atanh t = Σ t^(2i+1)/(2i+1) for 0 ≤ t ≤ 1/3, of width about 2^-p. -/
def atanh (p : Nat) (t : Rat) : Rat × Rat :=
  let q := guard p
  let t2 := t * t
  let eps : Rat := mkRat 1 (2 ^ (p + 2))
  let rec go : Nat → Nat → Rat → Rat → Rat → Rat → Rat × Rat
    | 0, _, _, ph, lo, hi => (lo, hi + ph * 9 / 8)
    | fuel + 1, i, pl, ph, lo, hi =>
      if ph * 9 / 8 ≤ eps then (lo, hi + ph * 9 / 8)
      else
        let d : Rat := ((2 * i + 1 : Nat) : Rat)
        go fuel (i + 1) (dn q (pl * t2)) (up q (ph * t2)) (lo + dn q (pl / d)) (hi + up q (ph / d))
  go (p + 16) 0 t t 0 0

/-- An enclosure of ln 2 = 2 atanh(1/3). -/
def ln2 (p : Nat) : Rat × Rat := let (a, b) := atanh p (1 / 3); (2 * a, 2 * b)

/-- ⌊log₂ x⌋ for x > 0. -/
def log2Floor (x : Rat) : Int :=
  let e0 : Int := (Nat.log2 x.num.natAbs : Int) - (Nat.log2 x.den : Int)
  if Binary64.ltPow2 x.num.natAbs x.den e0 then e0 - 1 else e0

/-- An enclosure of ln x for x > 0: k ln 2 + 2 atanh((m − 1)/(m + 1)), x = 2^k m, 1 ≤ m < 2. -/
def lnCore (p : Nat) (x : Rat) : Rat × Rat :=
  let k := log2Floor x
  let m := x / Binary64.pow2 k
  let (a, b) := atanh p ((m - 1) / (m + 1))
  let (l, h) := ln2 (p + 12 + Nat.log2 (k.natAbs + 1))
  if 0 ≤ k then (k * l + 2 * a, k * h + 2 * b) else (k * h + 2 * a, k * l + 2 * b)

/-- An enclosure of ln x for x > 0; an x of more than 4·guard bits between two of guard + 4 bits
(its numerator and denominator truncated). -/
def ln (p : Nat) (x : Rat) : Rat × Rat :=
  let q := guard p + 4
  let n := x.num.natAbs
  let d := x.den
  if Nat.log2 n + Nat.log2 d ≤ 4 * q then lnCore p x
  else
    let sn := Nat.log2 n - min (Nat.log2 n) q
    let sd := Nat.log2 d - min (Nat.log2 d) q
    let s := Binary64.pow2 ((sn : Int) - sd)
    let up (m k : Nat) := if k = 0 then m else (m >>> k) + 1
    ((lnCore p (mkRat (n >>> sn : Nat) (up d sd) * s)).1, (lnCore p (mkRat (up n sn : Nat) (d >>> sd) * s)).2)

/-- An enclosure of exp a for 0 ≤ a ≤ 1: Σ a^i/i!, the tail at most twice its first term
from the third term on. -/
def expPos (p : Nat) (a : Rat) : Rat × Rat :=
  let q := guard p
  let eps : Rat := mkRat 1 (2 ^ (p + 2))
  let rec go : Nat → Nat → Rat → Rat → Rat → Rat → Rat × Rat
    | 0, _, _, th, lo, hi => (lo, hi + 2 * th)
    | fuel + 1, i, tl, th, lo, hi =>
      if 2 ≤ i ∧ 2 * th ≤ eps then (lo, hi + 2 * th)
      else
        let d : Rat := ((i + 1 : Nat) : Rat)
        go fuel (i + 1) (dn q (tl * a / d)) (up q (th * a / d)) (lo + tl) (hi + th)
  go (p + 16) 0 1 1 0 0

/-- An enclosure of exp a for |a| ≤ 1. -/
def exp (p : Nat) (a : Rat) : Rat × Rat :=
  if 0 ≤ a then expPos p a
  else let (l, h) := expPos (p + 2) (-a); (dn (guard p) (1 / h), up (guard p) (1 / l))

/-- The bits of |e| above the point. -/
def magBits (e : Rat) : Nat := Nat.log2 e.num.natAbs + 1 - Nat.log2 e.den

/-- The bits of a rational's numerator and denominator. -/
def bits (q : Rat) : Nat := Nat.log2 q.num.natAbs + Nat.log2 q.den + 2

/-- An enclosure of b^e = exp(e ln b) for b > 0; `.error true` when e ln b is above 800 (the
value rounds to +∞), `.error false` when below -800 (to +0). -/
def encl (p : Nat) (b e : Rat) : Except Bool (Rat × Rat) :=
  let (l, h) := ln (p + magBits e + 4) b
  let (L, H) := if 0 ≤ e then (e * l, e * h) else (e * h, e * l)
  if 800 < L then .error true
  else if H < -800 then .error false
  else
    let n : Int := ((L + H) / 2 * 1442695040888963 / 1000000000000000 + 1 / 2).floor
    let (l2, h2) := ln2 (p + 16)
    let (rl, rh) := if 0 ≤ n then (L - n * h2, H - n * l2) else (L - n * l2, H - n * h2)
    let s := Binary64.pow2 n
    .ok (s * (exp (p + 4) rl).1, s * (exp (p + 4) rh).2)

/-- The rounding of b^e (b > 0, b^e not a binary64 value or a tie): the enclosure refined from 64
bits, doubling. -/
def toNum (b e : Rat) : BitVec 64 :=
  let rec go : Nat → Nat → BitVec 64
    | fuel, p => match encl p b e with
      | .error big => if big then Binary64.posInfinity else Binary64.posZero
      | .ok (l, h) =>
        let x := Binary64.ofRat l
        match fuel with
        | 0 => Binary64.ofRat ((l + h) / 2)
        | fuel + 1 => if x == Binary64.ofRat h then x else go fuel (2 * p)
  go 6 64

/-- ⌊n^(1/k)⌋ when n is a k-th power. -/
def root? (k n : Nat) : Option Nat :=
  if n ≤ 1 then some n
  else if Nat.log2 n + 1 < k then none
  else
    let rec go : Nat → Nat → Nat → Nat
      | 0, lo, _ => lo
      | fuel + 1, lo, hi => if hi ≤ lo + 1 then lo
        else let mid := (lo + hi) / 2
          if mid ^ k ≤ n then go fuel mid hi else go fuel lo mid
    let r := go (Nat.log2 n + 2) 1 (2 ^ (Nat.log2 n / k + 1))
    if r ^ k = n then some r else none

end Engine.RPow
