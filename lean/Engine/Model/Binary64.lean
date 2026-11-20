module

@[expose] public section

/-!
# IEEE 754-2019 binary64, for the fast model

The binary64 definitions (no theorems) that `Bare` uses. `ofRat` rounds an
exact rational to nearest, ties to even (ECMA-262 §6.1.6.1 "the Number value
for x"); the operations are computed exactly on `toRat` and rounded once.
`sqrtQ` is the correctly rounded square root of any non-negative rational.
-/

namespace Engine.Binary64

/-- The sign bit (bit 63). -/
def sign (b : BitVec 64) : Bool := b.msb

/-- The 11-bit biased exponent field. -/
def biasedExponent (b : BitVec 64) : Nat := (b.toNat / (1 <<< 52)) % 2 ^ 11

/-- The 52-bit fraction field. -/
def fraction (b : BitVec 64) : Nat := b.toNat % 2 ^ 52

def isNaN (b : BitVec 64) : Bool := biasedExponent b == 2047 && fraction b != 0
def isInfinite (b : BitVec 64) : Bool := biasedExponent b == 2047 && fraction b == 0
def isFinite (b : BitVec 64) : Bool := biasedExponent b != 2047
def isZero (b : BitVec 64) : Bool := biasedExponent b == 0 && fraction b == 0

/-- The canonical quiet NaN. -/
def qNaN : BitVec 64 := 0x7FF8000000000000#64
def posInfinity : BitVec 64 := 0x7FF0000000000000#64
def negInfinity : BitVec 64 := 0xFFF0000000000000#64
def posZero : BitVec 64 := 0#64
def negZero : BitVec 64 := 0x8000000000000000#64

/-- 2^e as an exact rational. -/
def pow2 (e : Int) : Rat :=
  if 0 ≤ e then ((2 ^ e.toNat : Nat) : Rat) else 1 / ((2 ^ (-e).toNat : Nat) : Rat)

/-- The exact value of a finite pattern (0 for NaN and the infinities): `m * 2^q`,
built directly when it is an integer. -/
def toRat (b : BitVec 64) : Rat :=
  if isFinite b then
    let e := biasedExponent b
    let m : Nat := if e = 0 then fraction b else fraction b + (1 <<< 52)
    let q : Int := (if e = 0 then (1 : Int) else e) - 1075
    let v : Rat :=
      if 0 ≤ q then ((m <<< q.toNat : Nat) : Rat)
      else if m % (1 <<< (-q).toNat) = 0 then ((m >>> (-q).toNat : Nat) : Rat)
      else (m : Rat) * pow2 q
    if sign b then -v else v
  else 0

/-- Assemble sign, biased exponent and fraction fields (the original's `BitVec.ofNat 64`, through
`UInt64` for speed). -/
def pack (neg : Bool) (biased frac : Nat) : BitVec 64 :=
  (UInt64.ofNat ((if neg then 1 <<< 63 else 0) + (biased <<< 52) + frac)).toBitVec

/-- `n / d < 2 ^ e`, exactly. -/
def ltPow2 (n d : Nat) (e : Int) : Bool :=
  if 0 ≤ e then n < d * 2 ^ e.toNat else n * 2 ^ (-e).toNat < d

/-- Round an exact rational to binary64: nearest, ties to even; magnitudes that
round to 2^1024 become infinities; a negative value that rounds to zero is -0. -/
def ofRat (x : Rat) : BitVec 64 :=
  if x = 0 then posZero else
  let neg := decide (x < 0)
  let n : Nat := x.num.natAbs
  let d : Nat := x.den
  -- An integer below 2^53 is exact: `n` shifted to 53 significant bits.
  if d = 1 ∧ n >>> 53 = 0 then
    let E := Nat.log2 n
    pack neg (E + 1023) ((n <<< (52 - E)) - (1 <<< 52))
  else
  -- ⌊log₂ |x|⌋ is `e0` or `e0 - 1`.
  let e0 : Int := (Nat.log2 n : Int) - (Nat.log2 d : Int)
  let E : Int := if ltPow2 n d e0 then e0 - 1 else e0
  -- The quantum: the weight of the last significand bit (subnormals share -1074).
  let q : Int := max E (-1022) - 52
  let num := if q ≤ 0 then n * 2 ^ (-q).toNat else n
  let den := if q ≤ 0 then d else d * 2 ^ q.toNat
  let m := num / den
  let r := num % den
  let m := if 2 * r > den ∨ (2 * r = den ∧ m % 2 = 1) then m + 1 else m
  -- Rounding up may carry into the next binade.
  let (m, q) := if m = 2 ^ 53 then (2 ^ 52, q + 1) else (m, q)
  if m < 2 ^ 52 then pack neg 0 m          -- subnormal or zero (q = -1074)
  else
    let biased : Int := q + 52 + 1023
    if 2047 ≤ biased then (if neg then negInfinity else posInfinity)
    -- `m < 2 ^ 53` here, so the `% 2 ^ 52` only drops the implicit bit.
    else pack neg biased.toNat ((m - 2 ^ 52) % 2 ^ 52)

/-! ## Arithmetic

The IEEE 754-2019 operations with roundTiesToEven, each computed exactly on
`toRat` and rounded once by `ofRat`. Every NaN result is `qNaN`. -/

/-- A zero with the given sign. -/
def zero (neg : Bool) : BitVec 64 := if neg then negZero else posZero

/-- An infinity with the given sign. -/
def infinity (neg : Bool) : BitVec 64 := if neg then negInfinity else posInfinity

/-- The pattern is -0. -/
def isNegZero (a : BitVec 64) : Bool := a == negZero

/-- negate: flip the sign bit (adding 2^63 modulo 2^64); NaN stays `qNaN`. -/
def neg (a : BitVec 64) : BitVec 64 :=
  if isNaN a then qNaN else BitVec.ofNat 64 ((a.toNat + 2 ^ 63) % 2 ^ 64)

/-! The four operations are defined as IEEE 754-2019 defines them: the exact result, rounded to nearest, ties to
even (`ofRat`). They run as the machine's binary64 operations (`addHw` and its like, `implemented_by`): that the
machine's are those operations is trusted, and `scripts/dev/binary64_check.lean` compares the two on random and
special operands. A NaN result is `qNaN`, whatever the machine's payload. -/

/-- A pattern as the machine's float, and back with one NaN. -/
@[inline] def toHw (a : BitVec 64) : Float := Float.ofBits a.toNat.toUInt64

@[inline] def ofHw (x : Float) : BitVec 64 := if x.isNaN then qNaN else BitVec.ofNat 64 x.toBits.toNat

def addHw (a b : BitVec 64) : BitVec 64 := ofHw (toHw a + toHw b)
def mulHw (a b : BitVec 64) : BitVec 64 := ofHw (toHw a * toHw b)
def divHw (a b : BitVec 64) : BitVec 64 := ofHw (toHw a / toHw b)

/-- addition. An exact zero sum is +0 unless both operands are -0. -/
@[implemented_by addHw]
def add (a b : BitVec 64) : BitVec 64 :=
  if isNaN a || isNaN b then qNaN
  else if isInfinite a then (if isInfinite b && sign a != sign b then qNaN else a)
  else if isInfinite b then b
  else if isNegZero a && isNegZero b then negZero
  else ofRat (toRat a + toRat b)

/-- multiplication. -/
@[implemented_by mulHw]
def mul (a b : BitVec 64) : BitVec 64 :=
  let s := sign a != sign b
  if isNaN a || isNaN b then qNaN
  else if isInfinite a || isInfinite b then (if isZero a || isZero b then qNaN else infinity s)
  else if isZero a || isZero b then zero s
  else ofRat (toRat a * toRat b)

/-- division. -/
@[implemented_by divHw]
def div (a b : BitVec 64) : BitVec 64 :=
  let s := sign a != sign b
  if isNaN a || isNaN b then qNaN
  else if isInfinite a then (if isInfinite b then qNaN else infinity s)
  else if isInfinite b then zero s
  else if isZero b then (if isZero a then qNaN else infinity s)
  else if isZero a then zero s
  else ofRat (toRat a / toRat b)

/-- Newton's iteration for ⌊√n⌋ from an overestimate `x`: it decreases
strictly until it reaches ⌊√n⌋, then stops (structural in the fuel). -/
def isqrtGo (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    let y := (x + n / x) / 2
    if y < x then isqrtGo n fuel y else x

/-- ⌊√n⌋. The start 2^(⌊log₂ n / 2⌋ + 1) is above √n and within a factor 2 of
it, so the precision doubles every step and 64 steps suffice far beyond
any `n` used here (n < 2^(2^60)). -/
def isqrt (n : Nat) : Nat := if n = 0 then 0 else isqrtGo n 64 (2 ^ (Nat.log2 n / 2 + 1))

/-- compareQuietLess: false when either operand is NaN; -0 and +0 are equal. -/
def lt (a b : BitVec 64) : Bool :=
  if isNaN a || isNaN b then false
  else if a = posInfinity || b = negInfinity then false
  else if b = posInfinity || a = negInfinity then true
  else toRat a < toRat b

/-- compareQuietEqual: false when either operand is NaN; -0 and +0 are equal. -/
def eq (a b : BitVec 64) : Bool :=
  if isNaN a || isNaN b then false
  else if isFinite a && isFinite b then toRat a == toRat b
  else a == b

/-- √x for a rational `x > 0`, rounded once: `⌊√(x·4^k)⌋` has ≥ 55 bits; an inexact root becomes `s + 1/2`. -/
def sqrtQ (x : Rat) : BitVec 64 :=
  let n := x.num.natAbs
  let d := x.den
  let k : Nat := (112 + Nat.log2 d - Nat.log2 n) / 2 + 1
  let N := n * 4 ^ k
  let M := N / d
  let s := isqrt M
  let root : Rat := if s * s = M ∧ M * d = N then (s : Rat) else (s : Rat) + 1 / 2
  ofRat (root * pow2 (-(k : Int)))

end Engine.Binary64
