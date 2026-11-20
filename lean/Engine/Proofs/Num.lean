module

public import Engine.Proofs.Binary64Ops
public import Engine.Proofs.Math
public import Engine.Proofs.Digits

@[expose] public section

/-!
# The laws of Numbers at the engine's model

A Number is a binary64 pattern with one NaN; its view is Binary64's over ℚ (`viewQ`), each value in its one
form (`ofQ`). So §6.1.6.1's laws (`Model.NumLaws`) are Binary64's (`Binary64Laws`, `Binary64Round`,
`Binary64Ops`), read through `toQ`; Number::toString's digits are `Digits.digits_spec`'s.
-/

namespace Engine.Model
open Ecma Engine.Binary64

/-- A view over ℚ as one over the engine's mathematical values. -/
def mapV : NumView Rat → NumView MathVal
  | .nan => .nan
  | .posInf => .posInf
  | .negInf => .negInf
  | .posZero => .posZero
  | .negZero => .negZero
  | .finite q => .finite (MathVal.ofQ q)

@[simp] theorem mapV_nan : mapV .nan = .nan := rfl
@[simp] theorem mapV_posInf : mapV .posInf = .posInf := rfl
@[simp] theorem mapV_negInf : mapV .negInf = .negInf := rfl
@[simp] theorem mapV_posZero : mapV .posZero = .posZero := rfl
@[simp] theorem mapV_negZero : mapV .negZero = .negZero := rfl
@[simp] theorem mapV_finite (q : Rat) : mapV (.finite q) = .finite (MathVal.ofQ q) := rfl

@[simp] theorem mapV_ite (c : Prop) [Decidable c] (u v : NumView Rat) :
    mapV (if c then u else v) = if c then mapV u else mapV v := by
  split <;> rfl

theorem numView_eq (b : BitVec 64) : numView b = mapV (viewQ b) := by
  unfold numView viewQ
  repeat' split <;> try rfl

/-- Making every NaN `qNaN` keeps the view. -/
theorem viewQ_of (b : BitVec 64) : viewQ (Num.of b).1 = viewQ b := by
  show viewQ (if isNaN b then qNaN else b) = _
  by_cases h : isNaN b = true
  · rw [if_pos h, viewQ_qNaN]; simp [viewQ, h]
  · rw [if_neg h]

namespace MathVal

theorem lt_eq (x y : MathVal) : lt x y = decide (x.toQ < y.toQ) := by
  cases h : lt x y with
  | true => exact (decide_eq_true ((lt_iff x y).1 h)).symm
  | false =>
    symm
    apply decide_eq_false
    intro h'
    rw [(lt_iff x y).2 h'] at h
    cases h

theorem eq_eq (x y : MathVal) : eq x y = decide (x.toQ = y.toQ) := by
  cases h : eq x y with
  | true => exact (decide_eq_true (congrArg toQ ((eq_iff x y).1 h))).symm
  | false =>
    symm
    apply decide_eq_false
    intro h'
    rw [(eq_iff x y).2 (toQ_inj h')] at h
    cases h

theorem toQ_nat (n : Nat) : (MathVal.int (n : Int)).toQ = (n : Rat) := by
  simp [toQ, Rat.intCast_natCast]

theorem toQ_pow2 (n : Nat) : (pow (.int ((2 : Nat) : Int)) (.int (n : Int))).toQ = (2 : Rat) ^ n := by
  rw [pow_nat, toQ_ofQ, toQ_nat]
  rfl

theorem toQ_sub (x y : MathVal) : (add x (neg y)).toQ = x.toQ - y.toQ := by
  rw [toQ_add, toQ_neg, Rat.sub_eq_add_neg]

end MathVal

end Engine.Model

namespace Engine.Impl
open Ecma Engine.Model Engine.Binary64

/-! The model's operations on mathematical values are `MathVal`'s. -/

theorem impl_ofNat (n : Nat) : Impl.ofNat n = MathVal.int (n : Int) := rfl
theorem impl_sub (a b : Impl.Math) : Impl.sub a b = MathVal.add a (MathVal.neg b) := rfl
theorem impl_neg (a : Impl.Math) : Impl.neg a = MathVal.neg a := rfl
theorem impl_pow (a b : Impl.Math) : Impl.pow a b = MathVal.pow a b := rfl
theorem impl_lt (a b : Impl.Math) : Impl.lt a b = MathVal.lt a b := rfl
theorem impl_eq (a b : Impl.Math) : Impl.eq a b = MathVal.eq a b := rfl

theorem toQ_form (neg : Bool) (m k : Nat) : MathVal.toQ (Model.form Impl neg m k) = formQ neg m k := by
  have h2 : ∀ n : Nat, (MathVal.pow (.int 2) (.int (n : Int))).toQ = (2 : Rat) ^ n := MathVal.toQ_pow2
  have h3 : (MathVal.pow (.int 2) (.int 1074)).toQ = (2 : Rat) ^ 1074 := h2 1074
  cases neg <;>
    simp [Model.form, formQ, signed, MathVal.toQ_div, MathVal.toQ_mul, MathVal.toQ_neg, h2, h3, Rat.intCast_natCast]

theorem finiteNum_iff (x : MathVal) (ev : Bool) : Model.finiteNum Impl x ev ↔ finiteQ x.toQ ev := by
  unfold Model.finiteNum finiteQ
  constructor
  · rintro ⟨neg, m, k, rfl, h⟩
    exact ⟨neg, m, k, toQ_form neg m k, h⟩
  · rintro ⟨neg, m, k, hx, h⟩
    exact ⟨neg, m, k, MathVal.toQ_inj (hx.trans (toQ_form neg m k).symm), h⟩

theorem toQ_two_pow_1024 : MathVal.toQ (Impl.pow (Impl.ofNat 2) (Impl.ofNat 1024)) = (2 : Rat) ^ 1024 := by
  rw [impl_pow, impl_ofNat, impl_ofNat]
  exact MathVal.toQ_pow2 1024

theorem toQ_neg_two_pow_1024 :
    MathVal.toQ (Impl.neg (Impl.pow (Impl.ofNat 2) (Impl.ofNat 1024))) = -((2 : Rat) ^ 1024) := by
  rw [impl_neg, MathVal.toQ_neg, toQ_two_pow_1024]

theorem candidate_iff (y : MathVal) (ev : Bool) : Model.candidate Impl y ev ↔ candQ y.toQ ev := by
  unfold Model.candidate candQ
  rw [finiteNum_iff]
  have h0 : y = Impl.ofNat 0 ↔ y.toQ = 0 :=
    ⟨fun h => by rw [h]; rfl, fun h => MathVal.toQ_inj (h.trans (by rfl))⟩
  have h1 : y = Impl.pow (Impl.ofNat 2) (Impl.ofNat 1024) ↔ y.toQ = 2 ^ 1024 :=
    ⟨fun h => by rw [h, toQ_two_pow_1024], fun h => MathVal.toQ_inj (h.trans toQ_two_pow_1024.symm)⟩
  have h2 : y = Impl.neg (Impl.pow (Impl.ofNat 2) (Impl.ofNat 1024)) ↔ y.toQ = -(2 ^ 1024) :=
    ⟨fun h => by rw [h, toQ_neg_two_pow_1024], fun h => MathVal.toQ_inj (h.trans toQ_neg_two_pow_1024.symm)⟩
  rw [h0, h1, h2]

theorem toQ_abs (x : Impl.Math) : MathVal.toQ (Model.abs Impl x) = absQ (MathVal.toQ x) := by
  simp only [Model.abs, impl_lt, impl_neg, impl_ofNat]
  rw [MathVal.lt_eq]
  unfold absQ
  have : (MathVal.int ((0 : Nat) : Int)).toQ = 0 := rfl
  rw [this]
  by_cases h : x.toQ < 0 <;> simp [h]

theorem toQ_absSub (x z : Impl.Math) :
    MathVal.toQ (Model.abs Impl (Impl.sub x z)) = absQ (MathVal.toQ x - MathVal.toQ z) := by
  rw [toQ_abs, impl_sub, MathVal.toQ_sub]

theorem nearest_iff (x y : MathVal) : Model.nearest Impl x y ↔ nearestQ x.toQ y.toQ := by
  unfold Model.nearest nearestQ
  constructor
  · rintro ⟨ev, hc, hall⟩
    refine ⟨ev, (candidate_iff y ev).1 hc, fun z ez hz => ?_⟩
    obtain ⟨h1, h2⟩ := hall (MathVal.ofQ z) ez ((candidate_iff _ _).2 (by rwa [MathVal.toQ_ofQ]))
    have e1 := toQ_absSub x (MathVal.ofQ z)
    have e2 := toQ_absSub x y
    rw [MathVal.toQ_ofQ] at e1
    refine ⟨fun hlt => ?_, fun heq hne => h2 (MathVal.toQ_inj (by rw [e1, e2, heq])) fun h => hne ?_⟩
    · have : Impl.lt (Model.abs Impl (Impl.sub x (MathVal.ofQ z))) (Model.abs Impl (Impl.sub x y)) = true :=
        (MathVal.lt_iff _ _).2 (by rw [e1, e2]; exact hlt)
      rw [this] at h1
      cases h1
    · rw [← h, MathVal.toQ_ofQ]
  · rintro ⟨ev, hc, hall⟩
    refine ⟨ev, (candidate_iff y ev).2 hc, fun z ez hz => ?_⟩
    obtain ⟨h1, h2⟩ := hall z.toQ ez ((candidate_iff _ _).1 hz)
    have e1 := toQ_absSub x z
    have e2 := toQ_absSub x y
    refine ⟨?_, fun heq hne => h2 (by rw [← e1, ← e2, heq]) fun h => hne (MathVal.toQ_inj h)⟩
    cases hl : Impl.lt (Model.abs Impl (Impl.sub x z)) (Model.abs Impl (Impl.sub x y)) with
    | false => rfl
    | true =>
      have := (MathVal.lt_iff _ _).1 hl
      rw [e1, e2] at this
      exact absurd this h1

theorem viewFor_eq (x y : Impl.Math) :
    Model.viewFor Impl x y = mapV (viewForQ (MathVal.toQ x) (MathVal.toQ y)) := by
  unfold Model.viewFor
  have h0 : MathVal.toQ (Impl.ofNat 0) = 0 := rfl
  simp only [impl_eq, impl_lt]
  rw [MathVal.eq_eq, MathVal.eq_eq, MathVal.eq_eq, MathVal.lt_eq, toQ_two_pow_1024, toQ_neg_two_pow_1024, h0]
  unfold viewForQ
  simp only [decide_eq_true_eq]
  by_cases a : MathVal.toQ y = 2 ^ 1024
  · simp only [if_pos a]; rfl
  · by_cases b : MathVal.toQ y = -(2 ^ 1024)
    · simp only [if_neg a, if_pos b]; rfl
    · by_cases c : MathVal.toQ y = 0
      · by_cases d : MathVal.toQ x < 0
        · simp only [if_neg a, if_neg b, if_pos c, if_pos d]; rfl
        · simp only [if_neg a, if_neg b, if_pos c, if_neg d]; rfl
      · simp only [if_neg a, if_neg b, if_neg c]
        show NumView.finite y = NumView.finite (MathVal.ofQ (MathVal.toQ y))
        rw [MathVal.ofQ_toQ]

/-! The views of the model's Numbers. -/

theorem view_eq (a : Impl.Num) : Impl.numView a = mapV (viewQ a.1) := numView_eq a.1

theorem view_of (b : BitVec 64) : Impl.numView (Num.of b) = mapV (viewQ b) := by
  rw [view_eq, viewQ_of]

theorem view_numOf (x : Impl.Math) : Impl.numView (Impl.numOf x) = mapV (viewQ (ofRat (MathVal.toQ x))) :=
  view_of _

theorem numView_nan : Impl.numView Impl.numNaN = .nan := by
  rw [view_eq]
  show mapV (viewQ qNaN) = _
  rw [viewQ_qNaN]
  rfl

theorem numView_inf : ∀ b, Impl.numView (Impl.numInf b) = if b then .negInf else .posInf := by
  intro b
  show Impl.numView (Num.of (infinity b)) = _
  rw [view_of, viewQ_infinity]
  cases b <;> rfl

theorem numView_zero : ∀ b, Impl.numView (Impl.numZero b) = if b then .negZero else .posZero := by
  intro b
  show Impl.numView (Num.of (zero b)) = _
  rw [view_of]
  cases b
  · show mapV (viewQ posZero) = _
    rw [viewQ_posZero]; rfl
  · show mapV (viewQ negZero) = _
    rw [viewQ_negZero]; rfl

/-- A view determines the Number value: the finite patterns by `toRat`, NaN by being `qNaN`. -/
theorem numView_inj (a b : Impl.Num) (h : Impl.numView a = Impl.numView b) : a = b := by
  rw [view_eq, view_eq] at h
  obtain ⟨a, ha⟩ := a; obtain ⟨b, hb⟩ := b
  apply Subtype.ext
  dsimp only at h ⊢
  rcases viewQ_cases a with ⟨va, na⟩ | ⟨va, rfl⟩ | ⟨va, rfl⟩ | ⟨va, rfl⟩ | ⟨va, rfl⟩ |
      ⟨x, va, -, -, hfa, hza, -, -, -, hx, -, -⟩ <;>
    rcases viewQ_cases b with ⟨vb, nb⟩ | ⟨vb, rfl⟩ | ⟨vb, rfl⟩ | ⟨vb, rfl⟩ | ⟨vb, rfl⟩ |
      ⟨y, vb, -, -, hfb, hzb, -, -, -, hy, -, -⟩ <;>
    (try rw [va] at h) <;> (try rw [vb] at h) <;> first | rfl | (cases h; done) | skip
  · rw [ha na, hb nb]
  · have e : MathVal.ofQ x = MathVal.ofQ y := NumView.finite.inj h
    have e := congrArg MathVal.toQ e
    rw [MathVal.toQ_ofQ, MathVal.toQ_ofQ] at e
    exact toRat_inj hfa hza hfb hzb (hx.trans (e.trans hy.symm))

theorem viewForQ_zero : viewForQ 0 0 = .posZero := by
  have := two_pow_1024_pos
  unfold viewForQ
  repeat' split <;> grind

theorem toQ_int0 : (MathVal.int 0).toQ = 0 := rfl

theorem view_toNum (x : MathVal) : numView (Num.of (MathVal.toNum x)).val = mapV (viewQ (ofRat x.toQ)) := by
  rw [numView_eq, viewQ_of]
  rfl

theorem ofQ_neg (q : Rat) : MathVal.ofQ (-q) = Impl.neg (MathVal.ofQ q) :=
  MathVal.toQ_inj (by rw [impl_neg, MathVal.toQ_neg, MathVal.toQ_ofQ, MathVal.toQ_ofQ])

/-! Number::toString's digits. -/

/-- r^z at an integer z, for r ≥ 2. -/
theorem toQ_pow_int {r : Nat} (hr : 2 ≤ r) (z : Int) : (MathVal.pow (.int r) (.int z)).toQ = (r : Rat) ^ z := by
  have e1 : (MathVal.int z).toQ.den = 1 := rfl
  have e2 : (MathVal.int z).toQ.num = z := rfl
  unfold MathVal.pow
  simp only [e1, e2, ite_true, MathVal.powInt_eq, MathVal.powIntExact, MathVal.toQ_ofQ]
  have e3 : (MathVal.int (r : Int)).toQ = (r : Rat) := Rat.intCast_natCast r
  rw [e3]
  split
  · rename_i h
    rw [← Rat.zpow_natCast]; congr 1; omega
  · rename_i h
    rw [← Rat.zpow_natCast, ← Rat.zpow_neg]; congr 1; omega

/-- A pattern as the model's Number is x exactly when it is x's pattern, for x not NaN. -/
theorem numOf_eq {x : Impl.Num} (hx : isNaN x.1 = false) (b : BitVec 64) : Num.of b = x ↔ b = x.1 := by
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    show b = x.1
    by_cases hb : isNaN b = true
    · have : Num.of b = Num.nan := Subtype.ext (by simp [Num.of, hb]; rfl)
      rw [h] at this
      have := congrArg Subtype.val this
      rw [this] at hx
      exact absurd hx (by decide)
    · simpa [Num.of, hb] using h1
  · intro h
    apply Subtype.ext
    show (if isNaN b then qNaN else b) = x.1
    rw [h, hx]; rfl

/-- `digitsOf` at the engine is `Digits.Valid` of the pattern. -/
theorem digitsOf_iff {x : Impl.Num} (hx : isNaN x.1 = false) {r : Nat} (hr : 2 ≤ r) (n : Int) (k : Nat) (s : Int) :
    Model.digitsOf Impl x (Impl.ofNat r) (.int n) k (.int s) ↔ Engine.Model.Digits.Valid x.1 r n k s := by
  have hp : ∀ j : Nat, (MathVal.pow (.int r) (.int (j : Int))).toQ = (((r : Int) ^ j : Int) : Rat) := fun j => by
    rw [toQ_pow_int hr, Engine.Model.Digits.hi_cast]
  unfold Model.digitsOf Engine.Model.Digits.Valid
  have e1 : Impl.lt (.int s) (Impl.pow (Impl.ofNat r) (Impl.ofNat (k - 1))) = false ↔ (r : Int) ^ (k - 1) ≤ s := by
    show MathVal.lt _ _ = false ↔ _
    rw [MathVal.lt_eq, decide_eq_false_iff_not, show MathVal.toQ (.int s) = (s : Rat) from rfl,
      show Impl.ofNat (k - 1) = MathVal.int ((k - 1 : Nat) : Int) from rfl, show Impl.ofNat r = MathVal.int (r : Int) from rfl,
      hp, Rat.not_lt, Rat.intCast_le_intCast]
  have e2 : Impl.lt (.int s) (Impl.pow (Impl.ofNat r) (Impl.ofNat k)) = true ↔ s < (r : Int) ^ k := by
    show MathVal.lt _ _ = true ↔ _
    rw [MathVal.lt_eq, decide_eq_true_iff, show MathVal.toQ (.int s) = (s : Rat) from rfl,
      show Impl.ofNat k = MathVal.int (k : Int) from rfl, show Impl.ofNat r = MathVal.int (r : Int) from rfl,
      hp, Rat.intCast_lt_intCast]
  have e3 : Impl.numOf (Impl.mul (.int s) (Impl.pow (Impl.ofNat r) (Impl.sub (.int n) (Impl.ofNat k)))) = x ↔
      ofRat ((s : Rat) * (r : Rat) ^ (n - k)) = x.1 := by
    show Num.of (ofRat (MathVal.toQ _)) = x ↔ _
    rw [numOf_eq hx, MathVal.toQ_mul, show MathVal.toQ (.int s) = (s : Rat) from rfl,
      show Impl.sub (.int n) (Impl.ofNat k) = MathVal.int (n + -(k : Int)) from rfl,
      show Impl.ofNat r = MathVal.int (r : Int) from rfl, toQ_pow_int hr, ← Int.sub_eq_add_neg]
  rw [e1, e2, e3]
  simp [MathVal.isInt]

/-- The engine's Number::toString digits meet step 5's condition with k least. -/
theorem numDigits_least (x : Impl.Num) (m : Impl.Math) (r : Nat) (hv : Impl.numView x = .finite m)
    (hm : Impl.lt (Impl.ofNat 0) m = true) (hr : 2 ≤ r) (_ : r ≤ 36) :
    Model.digitsOf Impl x (Impl.ofNat r) (Impl.numDigits x (Impl.ofNat r)).1 (Impl.numDigits x (Impl.ofNat r)).2.1
        (Impl.numDigits x (Impl.ofNat r)).2.2 ∧
      ∀ n k s, Model.digitsOf Impl x (Impl.ofNat r) n k s → (Impl.numDigits x (Impl.ofNat r)).2.1 ≤ k := by
  rw [view_eq] at hv
  rcases viewQ_cases x.1 with ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ |
      ⟨X, va, hn, -, -, -, -, -, -, -, -, -⟩ <;> rw [va] at hv <;> cases hv
  have hX : 0 < X := by
    have := (MathVal.lt_iff _ _).1 hm
    rwa [MathVal.toQ_ofQ] at this
  obtain ⟨h1, h2⟩ := Engine.Model.Digits.digits_spec (b := x.1) hr ⟨va, hX⟩
  have e : Impl.numDigits x (Impl.ofNat r) = (.int (Engine.Model.Digits.digits x.1 r).1,
      (Engine.Model.Digits.digits x.1 r).2.1, .int (Engine.Model.Digits.digits x.1 r).2.2) := rfl
  rw [e]
  refine ⟨(digitsOf_iff hn hr _ _ _).2 h1, fun n k s hd => ?_⟩
  have ⟨_, hni, hsi, _⟩ := hd
  cases n with
  | int n =>
    cases s with
    | int s => exact h2 n k s ((digitsOf_iff hn hr _ _ _).1 hd)
    | frac => cases hsi
  | frac => cases hni

/-- The engine's Numbers meet the Number laws. -/
theorem numLaws : Model.NumLaws Impl where
  numView_inj := numView_inj
  numView_finite a m h := by
    rw [view_eq] at h
    rcases viewQ_cases a.1 with ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ | ⟨va, -⟩ |
        ⟨x, va, -, -, hf, hz, -, -, -, hx, -, -⟩ <;> rw [va] at h <;> cases h
    exact ⟨_, (finiteNum_iff _ _).2 (by rw [MathVal.toQ_ofQ]; exact hx ▸ toRat_finiteQ hf hz)⟩
  finiteNum_view m ev h := by
    obtain ⟨b, hf, hz, hb⟩ := finiteQ_pattern ((finiteNum_iff _ _).1 h)
    have hn : isNaN b = false := by
      simp only [isFinite, isNaN, bne_iff_ne, ne_eq] at hf ⊢; simp [hf]
    refine ⟨⟨b, fun h => absurd h (by simp [hn])⟩, ?_⟩
    show Engine.Model.numView b = .finite m
    rw [numView_eq]
    simp [viewQ, hn, hf, hz, hb, MathVal.ofQ_toQ]
  numOf_nearest x := by
    by_cases hx : MathVal.toQ x = 0
    · refine ⟨x, (nearest_iff x x).2 (nearestQ_self (ev := true) (.inr (.inl ⟨hx, rfl⟩))), ?_⟩
      rw [view_numOf, viewFor_eq, hx, ofRat_zero, viewQ_posZero, viewForQ_zero]
    · obtain ⟨y, hn, hv⟩ := ofRat_view hx
      refine ⟨MathVal.ofQ y, (nearest_iff _ _).2 (by rwa [MathVal.toQ_ofQ]), ?_⟩
      rw [view_numOf, hv, viewFor_eq, MathVal.toQ_ofQ]
  numNeg_view a := by
    show Impl.numView (Num.of (neg a.1)) = _
    rw [view_of, neg_view, view_eq]
    generalize viewQ a.1 = va
    cases va <;> simp [ofQ_neg]
  numAdd_view a b := by
    show Impl.numView (Num.of (add a.1 b.1)) = _
    rw [view_of, add_view, view_eq, view_eq]
    generalize viewQ a.1 = va; generalize viewQ b.1 = vb
    cases va <;> cases vb <;> simp [realQ, Model.realOf, MathVal.eq_eq, view_toNum, toQ_int0, MathVal.toQ_ofQ] <;>
      intro h <;> rw [h, viewQ_ofRat_zero] <;> rfl
  numSub_def _ _ := rfl
  numMul_view a b := by
    show Impl.numView (Num.of (mul a.1 b.1)) = _
    rw [view_of, mul_view, view_eq, view_eq]
    generalize viewQ a.1 = va; generalize viewQ b.1 = vb
    cases va <;> cases vb <;> simp [realQ, Model.realOf, MathVal.eq_eq, MathVal.lt_eq, view_toNum, toQ_int0, MathVal.toQ_ofQ]
  numDiv_view a b := by
    show Impl.numView (Num.of (div a.1 b.1)) = _
    rw [view_of, div_view, view_eq, view_eq]
    generalize viewQ a.1 = va; generalize viewQ b.1 = vb
    cases va <;> cases vb <;> simp [realQ, Model.realOf, MathVal.eq_eq, MathVal.lt_eq, view_toNum, toQ_int0, MathVal.toQ_ofQ]
  numLt_def a b := by
    show Binary64.lt a.1 b.1 = _
    rw [lt_view, view_eq, view_eq]
    generalize viewQ a.1 = va; generalize viewQ b.1 = vb
    cases va <;> cases vb <;> simp [realQ, Model.realOf, MathVal.lt_eq, toQ_int0, MathVal.toQ_ofQ]
  numEq_def a b := by
    show Binary64.eq a.1 b.1 = _
    rw [eq_view, view_eq, view_eq]
    generalize viewQ a.1 = va; generalize viewQ b.1 = vb
    cases va <;> cases vb <;> simp [realQ, Model.realOf, MathVal.eq_eq, toQ_int0, MathVal.toQ_ofQ]
  numDigits_least := numDigits_least

end Engine.Impl
