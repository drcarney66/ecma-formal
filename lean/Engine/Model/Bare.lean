module

public import Ecma.Model
public import Engine.Model.Case
public import Engine.Model.Binary64
public import Engine.Model.RPow
public import Engine.Model.PropSets
public import Engine.Model.Normalize
public import Std.Data.HashMap

@[expose] public section

/-!
# The engine's values

What the engine's model (`Engine.Impl`) is made of. Mathematical values are the rationals, exactly: an integer
apart (the common case), any other as a `Rat`, one form for each value, so that equal values are equal terms
and the laws of §5.2.6 hold with `=`. The irrational results the specification names (a square root, π, a
function of §21.3, a power at a non-integer exponent) are their binary64 values as rationals: where the result is
rational it is exact, and where it is not, a Number is all the specification makes of it (𝔽 of a square root,
which is correctly rounded here, or an implementation-approximated value, where any approximation is allowed).
Numbers are binary64 bit patterns with IEEE 754-2019 arithmetic; BigInts are integers; Strings are arrays of
UTF-16 code units; Lists and the store are arrays; Records and property tables are hash-indexed maps that keep
creation order. Unicode property values are the pinned UCD's (`Engine.PropSets`).

A power at an integer exponent is exact whatever its size; the engine's step gives up at one too large to form
(`powSize`, past `maxBits`), as a machine that has run out of memory does. Number exponentiation is the host's
(`numPow`), from the two Numbers, without the exact power.
-/

namespace Engine.Model

open Ecma

/-- A mathematical value: a rational. An integer is `int`, any other rational `frac`, so each value has one
form. -/
inductive MathVal where
  | int (i : Int)
  | frac (q : Rat) (h : q.den ≠ 1)

instance : Inhabited MathVal := ⟨.int 0⟩

def piLo : Rat := (31415926535897932384626433832795028841971693993751058209749445923078164 : Nat) / (10 ^ 70 : Nat)

def piHi : Rat := piLo + 1 / (10 ^ 70 : Nat)

namespace MathVal

/-- The value. -/
@[inline] def toQ : MathVal → Rat
  | .int i => (i : Rat)
  | .frac q _ => q

/-- The value's form. -/
@[inline] def ofQ (q : Rat) : MathVal := if h : q.den = 1 then .int q.num else .frac q h

/-- The square root of a non-negative rational, when it is rational. -/
def sqrtQ? (q : Rat) : Option Rat :=
  let n := Binary64.isqrt q.num.natAbs
  let d := Binary64.isqrt q.den
  if 0 ≤ q ∧ n * n = q.num.natAbs ∧ d * d = q.den then some ((n : Rat) / (d : Rat)) else none

/-- c·π rounded: the rounding of both ends of π's enclosure when they agree, else of its midpoint. -/
def piNum (c : Rat) : BitVec 64 :=
  let a := Binary64.ofRat (c * piLo)
  if a == Binary64.ofRat (c * piHi) then a else Binary64.ofRat (c * (piLo + piHi) / 2)

/-- `n = b^k` for a natural `k`: `k`. -/
def logOf? (b n : Nat) : Option Nat :=
  let rec go : Nat → Nat → Nat → Option Nat
    | 0, _, _ => none
    | fuel + 1, m, k => if m = 1 then some k else if m % b = 0 then go fuel (m / b) (k + 1) else none
  if b < 2 ∨ n = 0 then none else go (Nat.log2 n + 1) n 0

/-- `q = b^k` for an integer `k`: `k`. -/
def logQ? (b : Nat) (q : Rat) : Option Int :=
  if q ≤ 0 then none
  else if q.den = 1 then (logOf? b q.num.natAbs).map fun k => (k : Int)
  else if q.num = 1 then (logOf? b q.den).map fun k => -(k : Int)
  else none

/-- The binary64 value of a rational, as a `Float`. -/
@[inline] def floatOf (q : Rat) : Float := Float.ofBits (Binary64.ofRat q).toNat.toUInt64

/-- 2⁻³⁰: below it, x ± x²/2 is e^x - 1 or ln(1 + x) to within binary64 (the next term is x³/6). -/
@[inline] def tinyF : Float := 9.313225746154785e-10

/-- ln(1 + d) for |d| < 1/2, as 2·atanh(d / (2 + d)); d - d²/2 for tiny d, where d / 2 underflows. -/
@[inline] def log1pF (d : Float) : Float :=
  if d.abs < tinyF then d - d * d / 2 else 2 * Float.atanh (d / (2 + d))

/-- e^x - 1 as tanh(x/2)·(e^x + 1); x + x²/2 for tiny x, where x / 2 underflows. -/
@[inline] def expm1F (x : Float) : Float :=
  if x.abs < tinyF then x + x * x / 2 else Float.tanh (x / 2) * (x.exp + 1)

/-- f(q) by libm, at the binary64 rounding of q (of q - 1 for ln near 1): not correctly rounded. -/
def fnFloat (f : MathFn) (q : Rat) : Float :=
  let x := floatOf q
  match f with
  | .sin => x.sin | .cos => x.cos | .tan => x.tan
  | .asin => x.asin | .acos => x.acos | .atan => x.atan
  | .sinh => x.sinh | .cosh => x.cosh | .tanh => x.tanh
  | .asinh => x.asinh | .acosh => x.acosh | .atanh => x.atanh
  | .exp => x.exp
  | .expm1 => expm1F x
  | .ln => if -half < q - 1 ∧ q - 1 < half then log1pF (floatOf (q - 1)) else x.log
  | .ln1p => if -half < q ∧ q < half then log1pF x else (floatOf (1 + q)).log
  | .log10 => x.log10 | .log2 => x.log2
  | .cbrt => x.cbrt
where half : Rat := 1 / 2

/-- ±f(q) by libm. -/
def fnNum (s : Bool) (f : MathFn) (q : Rat) : BitVec 64 :=
  let r := BitVec.ofNat 64 (fnFloat f q).toBits.toNat
  if s then Binary64.neg r else r

/-- A Number's value as a mathematical value: a finite one's; ±2^1100 for an infinity (it rounds back to it); 0
for NaN. -/
def ofNum (b : BitVec 64) : MathVal :=
  if Binary64.isNaN b then .int 0
  else if Binary64.isInfinite b then .int (if Binary64.sign b then -(2 ^ 1100 : Int) else 2 ^ 1100)
  else ofQ (Binary64.toRat b)

@[inline] def neg (x : MathVal) : MathVal := match x with
  | .int i => .int (-i)
  | x => ofQ (-toQ x)

@[inline] def add (x y : MathVal) : MathVal := match x, y with
  | .int a, .int b => .int (a + b)
  | x, y => ofQ (toQ x + toQ y)

@[inline] def mul (x y : MathVal) : MathVal := match x, y with
  | .int a, .int b => .int (a * b)
  | x, y => ofQ (toQ x * toQ y)

/-- x / y; 0 where y is 0. -/
def div (x y : MathVal) : MathVal := ofQ (toQ x / toQ y)

@[inline] def lt (x y : MathVal) : Bool := match x, y with
  | .int a, .int b => decide (a < b)
  | x, y => decide (toQ x < toQ y)

@[inline] def eq (x y : MathVal) : Bool := match x, y with
  | .int a, .int b => a == b
  | x, y => toQ x == toQ y

@[inline] def isInt : MathVal → Bool
  | .int _ => true
  | .frac .. => false

def floor : MathVal → MathVal
  | .int i => .int i
  | .frac q _ => .int q.floor

/-- a^n, exactly. -/
def powIntExact (a : Rat) (n : Int) : MathVal :=
  ofQ (if 0 ≤ n then a ^ n.toNat else (a ^ (-n).toNat)⁻¹)

/-- a^n for an integer n: `powIntExact`, with 0, 1 and -1 at any exponent without a power. -/
def powInt (a : Rat) (n : Int) : MathVal :=
  if a = 0 then .int (if n = 0 then 1 else 0)
  else if a = 1 then .int 1
  else if a = -1 then .int (if n % 2 = 0 then 1 else -1)
  else powIntExact a n

/-- The size of a^n in bits, estimated from a's: n · (⌊log₂ |num a|⌋ + ⌊log₂ (den a)⌋) + 1, the bit length of a
power of 2 exactly and at least half that of any other a^n. -/
def powBits (a : Rat) (n : Int) : Nat := n.natAbs * (Nat.log2 a.num.natAbs + Nat.log2 a.den) + 1

/-- x^y: exact for an integer y, and for a positive x whose root y asks for is rational; else the binary64 value
of the power (correctly rounded); 0 for x ≤ 0 and a non-integer y. -/
def pow (x y : MathVal) : MathVal :=
  let a := toQ x
  let e := toQ y
  if e.den = 1 then powInt a e.num
  else if a ≤ 0 then .int 0
  else match RPow.root? e.den a.num.natAbs, RPow.root? e.den a.den with
    | some r, some s => powInt ((r : Rat) / (s : Rat)) e.num
    | _, _ => ofNum (RPow.toNum a e)

/-- The bits `pow x y` forms as an exact power (`powBits`): 0 where it forms none (a base 0, 1 or -1; a non-integer
exponent without a rational root). -/
def powSize (x y : MathVal) : Nat :=
  let a := toQ x
  let e := toQ y
  if a = 0 ∨ a = 1 ∨ a = -1 then 0
  else if e.den = 1 then powBits a e.num
  else if a ≤ 0 then 0
  else match RPow.root? e.den a.num.natAbs, RPow.root? e.den a.den with
    | some r, some s => powBits ((r : Rat) / (s : Rat)) e.num
    | _, _ => 0

/-- The engine's limit on an exact power it forms (`powSize`), in bits: 2^30, V8's limit on a BigInt. -/
def maxBits : Nat := 1 <<< 30

/-- `q = 2^k`: k. -/
def log2Exact? (q : Rat) : Option Int :=
  let n := q.num.natAbs
  let d := q.den
  if q ≤ 0 then none
  else if d = 1 ∧ n = 1 <<< Nat.log2 n then some (Nat.log2 n : Int)
  else if n = 1 ∧ d = 1 <<< Nat.log2 d then some (-(Nat.log2 d : Int))
  else none

/-- a^n rounded to binary64 for a rational a > 0 and an integer n: exactly where the power is small (|n| ≤ 64, or
at most 2^20 bits); for a power of 2 from its exponent; else by `RPow.toNum`, for an a^n that is neither a binary64
value nor a tie (its odd part, the |n|th power of an odd integer above 1, has more than 54 bits, or it is not
dyadic). -/
def numPowPos (a : Rat) (n : Int) : BitVec 64 :=
  if n.natAbs ≤ 64 ∨ n.natAbs * RPow.bits a ≤ 1 <<< 20 then Binary64.ofRat (powIntExact a n).toQ
  else match log2Exact? a with
    | some k =>
      let j := k * n
      if 1100 < j then Binary64.posInfinity else if j < -1100 then Binary64.posZero
      else Binary64.ofRat (Binary64.pow2 j)
    | none => RPow.toNum a (n : Rat)

/-- The implementation-approximated value of x^y for binary64 x and y (Number::exponentiate step 13, `ApproxPower`):
for finite non-zero x and y, x > 0 or y an integer, the rounding of the real power, correctly rounded wherever
`RPow.toNum`'s refinement settles; NaN for the other operands, which the steps above decide. -/
def numPow (x y : BitVec 64) : BitVec 64 :=
  if !(Binary64.isFinite x && Binary64.isFinite y) || Binary64.isZero x || Binary64.isZero y then Binary64.qNaN
  else
    let a := Binary64.toRat x
    let e := Binary64.toRat y
    let neg := decide (a < 0)
    if neg && e.den != 1 then Binary64.qNaN
    else
      let b := if neg then -a else a
      let r := if e.den = 1 then numPowPos b e.num
        else match RPow.root? e.den b.num.natAbs, RPow.root? e.den b.den with
          | some p, some q => numPowPos ((p : Rat) / (q : Rat)) e.num
          | _, _ => RPow.toNum b e
      if neg && e.num % 2 != 0 then Binary64.neg r else r

/-- √x: exact where it is rational, else its binary64 value (correctly rounded); 0 for a negative x. -/
def sqrt (x : MathVal) : MathVal :=
  let q := toQ x
  if q < 0 then .int 0
  else match sqrtQ? q with
    | some r => ofQ r
    | none => ofNum (Binary64.sqrtQ q)

/-- c·π as its binary64 value. -/
def piTimes (c : Rat) : MathVal := if c = 0 then .int 0 else ofNum (piNum c)

/-- f(x): the exact value where it is rational, a multiple of π as its binary64 value, else libm's (`fnNum`); 0
outside f's domain. -/
def mathFn (f : MathFn) (x : MathVal) : MathVal :=
  let q := toQ x
  let half : Rat := 1 / 2
  let fl : MathVal := ofNum (fnNum false f q)
  match f with
  | .sin | .tan | .atan | .sinh | .tanh | .asinh | .expm1 =>
    if q = 0 then .int 0
    else if f == .atan ∧ (q = 1 ∨ q = -1) then piTimes (q / 4)
    else fl
  | .cos | .cosh | .exp => if q = 0 then .int 1 else fl
  | .asin | .acos =>
    if q < -1 ∨ 1 < q then .int 0
    else if q = 0 ∨ q = 1 ∨ q = -1 ∨ q = half ∨ q = -half then
      let c : Rat := if q = 0 then 0 else if q = 1 then half else if q = -1 then -half
        else if q = half then 1 / 6 else -1 / 6
      piTimes (if f == .asin then c else half - c)
    else fl
  | .acosh => if q ≤ 1 then .int 0 else fl
  | .atanh => if q ≤ -1 ∨ 1 ≤ q ∨ q = 0 then .int 0 else fl
  | .ln1p => if q ≤ -1 ∨ q = 0 then .int 0 else fl
  | .ln | .log10 | .log2 =>
    if q ≤ 0 then .int 0
    else match f, logQ? 2 q, logQ? 10 q with
      | .ln, _, _ => if q = 1 then .int 0 else fl
      | .log2, some k, _ => .int k
      | .log10, _, some k => .int k
      | _, _, _ => fl
  | .cbrt =>
    let a := if q < 0 then -q else q
    match RPow.root? 3 a.num.natAbs, RPow.root? 3 a.den with
    | some n, some d => ofQ (if q < 0 then -((n : Rat) / d) else (n : Rat) / d)
    | _, _ => fl

/-- 𝔽(x): roundTiesToEven. -/
def toNum (x : MathVal) : BitVec 64 := Binary64.ofRat (toQ x)

/-- ℤ(x) for an integer x; the floor of another. -/
def bigOf : MathVal → Int
  | .int i => i
  | .frac q _ => q.floor

/-- The index a mathematical value names: a non-negative integer. -/
@[inline] def idx : MathVal → Option Nat
  | .int i => if 0 ≤ i then some i.toNat else none
  | _ => none

end MathVal

/-- The case view of a binary64 pattern (§6.1.6.1). -/
def numView (b : BitVec 64) : NumView MathVal :=
  if Binary64.isNaN b then .nan
  else if Binary64.isFinite b = false then (if Binary64.sign b then .negInf else .posInf)
  else if Binary64.isZero b then (if Binary64.sign b then .negZero else .posZero)
  else .finite (MathVal.ofQ (Binary64.toRat b))

/-- A Number value: a binary64 pattern, with one NaN (§6.1.6.1). -/
def Num := {b : BitVec 64 // Binary64.isNaN b = true → b = Binary64.qNaN}

open Binary64 in
/-- A pattern as a Number value: every NaN is `qNaN`. -/
@[inline] def Num.of (b : BitVec 64) : Num :=
  ⟨if isNaN b then qNaN else b, fun h => by by_cases hb : isNaN b = true <;> simp_all⟩

/-- NaN. -/
def Num.nan : Num := ⟨Binary64.qNaN, fun _ => rfl⟩

/-- A Number's pattern. -/
@[inline] def Num.bits (a : Num) : BitVec 64 := a.1

instance : BEq Num := ⟨fun a b => a.1 == b.1⟩

abbrev NodeKey := Nat × Nat × Nat × NtId

/-- A Parse Node: its parse's stamp and its span, its production, nonterminal and parameters, its children with
their nonterminals, and its source text (a view of the parsed code points). -/
inductive Node where
  | mk (stamp lo hi : Nat) (prod : ProdId) (nt : NtId) (args : List Ecma.Grammar.Param) (kids : Array (NtId × Option Node))
    (text : Subarray Nat)

/-- A tree's parent index (`Engine.index`): its nodes, and each node's key to its parent (0 the root, `k + 1` the
`k`-th). -/
abbrev Index := Array Node × Std.HashMap NodeKey Nat

/-- Grammar parameters are decidably equal. -/
instance decEqParam : DecidableEq Ecma.Grammar.Param := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

/-- Views of source text are decidably equal: the same text, start and end. -/
instance decEqText : DecidableEq (Subarray Nat) := fun a b =>
  decidable_of_iff (a.array = b.array ∧ a.start = b.start ∧ a.stop = b.stop) (by
    obtain ⟨⟨a1, a2, a3, a4, a5⟩⟩ := a
    obtain ⟨⟨b1, b2, b3, b4, b5⟩⟩ := b
    constructor
    · rintro ⟨h1, h2, h3⟩
      cases h1; cases h2; cases h3; rfl
    · intro h; cases h; exact ⟨rfl, rfl, rfl⟩)

mutual
/-- Whether two Parse Nodes are equal, field by field. -/
def Node.eqB : Node → Node → Bool
  | .mk k i j p n as ks t, .mk k' i' j' p' n' as' ks' t' =>
    k == k' && i == i' && j == j' && p == p' && n == n' && decide (as = as') && Node.arrEqB ks ks' &&
      decide (t = t')

/-- Whether two arrays of children are equal. -/
def Node.arrEqB : Array (NtId × Option Node) → Array (NtId × Option Node) → Bool
  | ⟨l⟩, ⟨l'⟩ => Node.kidsEqB l l'

/-- Whether two child lists are equal, child by child. -/
def Node.kidsEqB : List (NtId × Option Node) → List (NtId × Option Node) → Bool
  | [], [] => true
  | (a, x) :: r, (b, y) :: r' => a == b && Node.optEqB x y && Node.kidsEqB r r'
  | _, _ => false

/-- Whether two optional children are equal. -/
def Node.optEqB : Option Node → Option Node → Bool
  | none, none => true
  | some x, some y => Node.eqB x y
  | _, _ => false
end

mutual
/-- `Node.eqB` holds of equal nodes only. -/
theorem Node.eqB_sound : ∀ a b : Node, Node.eqB a b = true → a = b
  | .mk .., .mk .., h => by
    simp only [Node.eqB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    subst h1 h2 h3 h4 h5 h6 h8; rw [Node.arrEqB_sound _ _ h7]

theorem Node.arrEqB_sound : ∀ a b : Array (NtId × Option Node), Node.arrEqB a b = true → a = b
  | ⟨l⟩, ⟨l'⟩, h => by
    simp only [Node.arrEqB] at h
    rw [Node.kidsEqB_sound _ _ h]

theorem Node.kidsEqB_sound : ∀ a b : List (NtId × Option Node), Node.kidsEqB a b = true → a = b
  | [], [], _ => rfl
  | (_, _) :: _, (_, _) :: _, h => by
    simp only [Node.kidsEqB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [h1, Node.optEqB_sound _ _ h2, Node.kidsEqB_sound _ _ h3]
  | [], _ :: _, h | _ :: _, [], h => by simp [Node.kidsEqB] at h

theorem Node.optEqB_sound : ∀ a b : Option Node, Node.optEqB a b = true → a = b
  | none, none, _ => rfl
  | some x, some y, h => by
    simp only [Node.optEqB] at h
    rw [Node.eqB_sound x y h]
  | none, some _, h | some _, none, h => by simp [Node.optEqB] at h
end

mutual
/-- A node is `Node.eqB` itself. -/
theorem Node.eqB_refl : ∀ a : Node, Node.eqB a a = true
  | .mk _ _ _ _ _ _ ks _ => by simp [Node.eqB, Node.arrEqB_refl ks]

theorem Node.arrEqB_refl : ∀ a : Array (NtId × Option Node), Node.arrEqB a a = true
  | ⟨l⟩ => by simp [Node.arrEqB, Node.kidsEqB_refl l]

theorem Node.kidsEqB_refl : ∀ a : List (NtId × Option Node), Node.kidsEqB a a = true
  | [] => by simp [Node.kidsEqB]
  | (_, x) :: r => by simp [Node.kidsEqB, Node.optEqB_refl x, Node.kidsEqB_refl r]

theorem Node.optEqB_refl : ∀ a : Option Node, Node.optEqB a a = true
  | none => by simp [Node.optEqB]
  | some x => by simp [Node.optEqB, Node.eqB_refl x]
end

/-- Parse Nodes are decidably equal: one object, or equal field by field. -/
instance decEqNode : DecidableEq Node := fun a b =>
  withPtrEqDecEq a b fun _ => decidable_of_iff (Node.eqB a b = true) ⟨Node.eqB_sound a b, fun h => h ▸ Node.eqB_refl a⟩

/-- Whether two Parse Nodes are the same. -/
def Node.same (a b : Node) : Bool := decide (a = b)

theorem Node.same_iff (a b : Node) : Node.same a b = true ↔ a = b := decide_eq_true_iff

/-- Collect the proper descendants of a Parse Node onto `acc`, in pre-order. -/
def descendantsInto : Array Node → Node → Array Node
  | acc, .mk _ _ _ _ _ _ kids _ => kids.attach.foldl (fun acc ⟨p, _h⟩ => match _hc : p.2 with
    | some c => descendantsInto (acc.push c) c
    | none => acc) acc
decreasing_by
  obtain ⟨a, b⟩ := p
  cases _hc
  have := Array.sizeOf_lt_of_mem _h
  simp only [Prod.mk.sizeOf_spec, Option.some.sizeOf_spec] at this
  simp only [Node.mk.sizeOf_spec]
  omega

/-- The proper descendants of a Parse Node, in pre-order. -/
def descendants (n : Node) : Array Node := descendantsInto #[] n

/-- A written occurrence's nonterminal: its child's, or the item's where it is absent. -/
def slotNt : NtId × Option Node → NtId
  | (_, some (.mk _ _ _ _ n _ _ _)) => n
  | (t, none) => t

/-- The `k`-th written occurrence of a nonterminal: its child, or none where an optional item is
absent; none outside where there is no such occurrence. -/
def nodeChild : Node → NtId → Nat → Option (Option Node)
  | .mk _ _ _ _ _ _ kids _, nt, k => ((kids.filter fun c => slotNt c == nt).map Prod.snd)[k]?

/-- A Parse Node's children. -/
def kidsOf : Node → Array Node
  | .mk _ _ _ _ _ _ kids _ => kids.filterMap Prod.snd

mutual
/-- One more than the depth of the tree below a Parse Node. -/
def Node.height : Node → Nat
  | .mk _ _ _ _ _ _ ks _ => Node.heightArr ks + 1

def Node.heightArr : Array (NtId × Option Node) → Nat
  | ⟨l⟩ => Node.heightList l

def Node.heightList : List (NtId × Option Node) → Nat
  | [] => 0
  | (_, x) :: r => max (Node.heightOpt x) (Node.heightList r)

def Node.heightOpt : Option Node → Nat
  | none => 0
  | some c => Node.height c
end

/-- The Parse Node of which `n` is a child, within the tree below `r` (to depth `f`): the first, a node before
its children's trees. -/
def parentBelow (n : Node) : Nat → Node → Option Node
  | 0, _ => none
  | f + 1, r =>
    if (kidsOf r).foldl (fun b c => b || decide (c = n)) false then some r
    else (kidsOf r).foldl (fun acc c => acc <|> parentBelow n f c) none

/-- The nodes above `n` by `parent`, the nearest first (to `f` of them). -/
def ancestorsBy (parent : Node → Option Node) : Nat → Node → List Node
  | 0, _ => []
  | f + 1, n => match parent n with
    | some p => p :: ancestorsBy parent f p
    | none => []

/-- The UTF-16 encoding of a string. -/
def utf16 (s : String) : Array UInt16 :=
  s.foldl (fun a c =>
    let v := c.val.toNat
    if v < 0x10000 then a.push v.toUInt16
    else (a.push (0xD800 + (v - 0x10000) / 0x400).toUInt16).push (0xDC00 + (v - 0x10000) % 0x400).toUInt16) #[]

/-- The UTF-16 encoding of code points. -/
def unitsOf (cs : Array Nat) : Array UInt16 :=
  cs.foldl (fun a c =>
    if c < 0x10000 then a.push c.toUInt16
    else (a.push (0xD800 + (c - 0x10000) / 0x400).toUInt16).push (0xDC00 + (c - 0x10000) % 0x400).toUInt16) #[]

/-- Property keys' equality: equal strings, or equal Symbols. -/
instance instBEqPropKey : BEq (Array UInt16 ⊕ (Nat × Option (Array UInt16))) where
  beq
    | .inl a, .inl b => a == b
    | .inr a, .inr b => a == b
    | _, _ => false

/-- A property key's hash. -/
instance : Hashable (Array UInt16 ⊕ (Nat × Option (Array UInt16))) where
  hash
    | .inl s => s.foldl (fun h u => mixHash h (hash u)) 7
    | .inr (n, _) => mixHash 11 (hash n)

/-- A map in creation order: its entries (a removed one leaves `none`) and their positions by key. -/
structure OMap (K : Type) [BEq K] [Hashable K] (α : Type) where
  entries : Array (Option (K × α))
  index : Std.HashMap K Nat

namespace OMap
variable {K α : Type} [BEq K] [Hashable K]

def empty : OMap K α := ⟨#[], {}⟩

def get (m : OMap K α) (k : K) : Option α :=
  match m.index[k]? with
  | some i => match m.entries[i]? with
    | some (some e) => some e.2
    | _ => none
  | none => none

/-- Update in place, or add at the end of creation order. -/
def put (m : OMap K α) (k : K) (a : α) : OMap K α :=
  match m.index[k]? with
  | some i => { m with entries := m.entries.setIfInBounds i (some (k, a)) }
  | none => ⟨m.entries.push (some (k, a)), m.index.insert k m.entries.size⟩

def del (m : OMap K α) (k : K) : OMap K α :=
  match m.index[k]? with
  | some i => ⟨m.entries.setIfInBounds i none, m.index.erase k⟩
  | none => m

/-- The keys in creation order. -/
def keys (m : OMap K α) : Array K := m.entries.filterMap fun e => e.map Prod.fst

end OMap

end Engine.Model
