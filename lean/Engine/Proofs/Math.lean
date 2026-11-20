module

public import Engine.Model

@[expose] public section

/-!
# The laws of mathematical values at the engine's model

`MathVal` is the rationals with one form for each value (`toQ`, `ofQ` are inverse), and each operation is the
rationals': so §5.2.6's laws (`Model.Laws`, from `add_assoc` to `isInt_iff`) are the rationals' own.
-/

namespace Engine.Model.MathVal

theorem ofQ_toQ (x : MathVal) : ofQ x.toQ = x := by
  cases x with
  | int i => simp [toQ, ofQ]
  | frac q h => simp [toQ, ofQ, h]

theorem toQ_ofQ (q : Rat) : (ofQ q).toQ = q := by
  unfold ofQ
  split
  · rename_i h
    obtain ⟨n, d, nz, c⟩ := q
    simp only at h
    subst h
    simp [toQ, Rat.mk_den_one]
  · rfl

theorem toQ_inj {x y : MathVal} (h : x.toQ = y.toQ) : x = y := by
  rw [← ofQ_toQ x, ← ofQ_toQ y, h]

@[simp] theorem toQ_int (i : Int) : (MathVal.int i).toQ = (i : Rat) := rfl

@[simp] theorem toQ_add (x y : MathVal) : (add x y).toQ = x.toQ + y.toQ := by
  unfold add
  split <;> simp [toQ_ofQ, Rat.intCast_add]

@[simp] theorem toQ_mul (x y : MathVal) : (mul x y).toQ = x.toQ * y.toQ := by
  unfold mul
  split <;> simp [toQ_ofQ, Rat.intCast_mul]

@[simp] theorem toQ_neg (x : MathVal) : (neg x).toQ = -x.toQ := by
  unfold neg
  split <;> simp [toQ_ofQ, Rat.intCast_neg]

@[simp] theorem toQ_div (x y : MathVal) : (div x y).toQ = x.toQ / y.toQ := by
  simp [div, toQ_ofQ]

theorem lt_iff (x y : MathVal) : lt x y = true ↔ x.toQ < y.toQ := by
  unfold lt
  split <;> simp [Rat.intCast_lt_intCast]

theorem eq_iff (x y : MathVal) : eq x y = true ↔ x = y := by
  constructor
  · intro h
    apply toQ_inj
    unfold eq at h
    split at h <;> simp_all
  · intro h
    subst h
    unfold eq
    split <;> simp


/-! §5.2.6's laws. -/

theorem ratLtTrans {a b c : Rat} (h₁ : a < b) (h₂ : b < c) : a < c := by
  rw [Rat.lt_iff_le_and_ne] at *
  refine ⟨Rat.le_trans h₁.1 h₂.1, fun h => ?_⟩
  subst h
  exact h₁.2 (Rat.le_antisymm h₁.1 h₂.1)

theorem ratTrichotomy (a b : Rat) : a < b ∨ a = b ∨ b < a := by
  rcases @Rat.le_total a b with h | h
  · rcases Rat.le_iff_lt_or_eq.1 h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · rcases Rat.le_iff_lt_or_eq.1 h with h | h
    · exact .inr (.inr h)
    · exact .inr (.inl h.symm)

theorem add_assoc (a b c : MathVal) : add (add a b) c = add a (add b c) :=
  toQ_inj (by simp [Rat.add_assoc])

theorem add_comm (a b : MathVal) : add a b = add b a :=
  toQ_inj (by simp [Rat.add_comm])

theorem add_zero (a : MathVal) : add a (.int 0) = a :=
  toQ_inj (by simp [Rat.add_zero])

theorem add_neg (a : MathVal) : add a (neg a) = .int 0 :=
  toQ_inj (by simp [Rat.add_neg_cancel])

theorem mul_assoc (a b c : MathVal) : mul (mul a b) c = mul a (mul b c) :=
  toQ_inj (by simp [Rat.mul_assoc])

theorem mul_comm (a b : MathVal) : mul a b = mul b a :=
  toQ_inj (by simp [Rat.mul_comm])

theorem mul_one (a : MathVal) : mul a (.int 1) = a :=
  toQ_inj (by simp)

theorem mul_add (a b c : MathVal) : mul a (add b c) = add (mul a b) (mul a c) :=
  toQ_inj (by simp [Rat.mul_add])

theorem div_mul (a b : MathVal) (h : b ≠ .int 0) : mul (div a b) b = a := by
  apply toQ_inj
  have hb : b.toQ ≠ 0 := fun h0 => h (toQ_inj (by simpa using h0))
  simp [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hb]

theorem zero_ne_one : (MathVal.int 0) ≠ .int 1 := by
  intro h; cases h

theorem lt_irrefl (a : MathVal) : lt a a = false := by
  cases h : lt a a with
  | false => rfl
  | true => exact absurd ((lt_iff a a).1 h) Rat.lt_irrefl

theorem lt_trans (a b c : MathVal) (h₁ : lt a b = true) (h₂ : lt b c = true) : lt a c = true :=
  (lt_iff a c).2 (ratLtTrans ((lt_iff a b).1 h₁) ((lt_iff b c).1 h₂))

theorem lt_total (a b : MathVal) : lt a b = true ∨ a = b ∨ lt b a = true := by
  rcases ratTrichotomy a.toQ b.toQ with h | h | h
  · exact .inl ((lt_iff a b).2 h)
  · exact .inr (.inl (toQ_inj h))
  · exact .inr (.inr ((lt_iff b a).2 h))

theorem add_lt_add (a b c : MathVal) (h : lt a b = true) : lt (add a c) (add b c) = true :=
  (lt_iff _ _).2 (by simpa [Rat.add_lt_add_right] using (lt_iff a b).1 h)

theorem mul_pos (a b : MathVal) (ha : lt (.int 0) a = true) (hb : lt (.int 0) b = true) :
    lt (.int 0) (mul a b) = true :=
  (lt_iff _ _).2 (by simpa using Rat.mul_pos (by simpa using (lt_iff _ a).1 ha) (by simpa using (lt_iff _ b).1 hb))

theorem ofNat_add (m n : Nat) : MathVal.int ((m + n : Nat) : Int) = add (.int m) (.int n) := by
  simp [add]

theorem floor_isInt (x : MathVal) : isInt (floor x) = true := by
  cases x <;> rfl

theorem toQ_floor (x : MathVal) : (floor x).toQ = (x.toQ.floor : Rat) := by
  cases x with
  | int i => simp [floor, Rat.floor_intCast]
  | frac q h => rfl

theorem floor_le (x : MathVal) : lt x (floor x) = false := by
  cases h : lt x (floor x) with
  | false => rfl
  | true =>
    have h1 := (lt_iff _ _).1 h
    rw [toQ_floor] at h1
    exact absurd h1 (Rat.not_lt.2 (Rat.floor_le _))

theorem lt_floor_add_one (x : MathVal) : lt x (add (floor x) (.int 1)) = true :=
  (lt_iff _ _).2 (by
    rw [toQ_add, toQ_floor]
    simpa [Rat.intCast_add] using Rat.lt_floor_add_one x.toQ)

theorem isInt_iff (x : MathVal) :
    isInt x = true ↔ ∃ n : Nat, x = .int n ∨ x = neg (.int n) := by
  constructor
  · intro h
    cases x with
    | int i =>
      refine ⟨i.natAbs, ?_⟩
      rcases Int.natAbs_eq i with e | e
      · exact .inl (by rw [← e])
      · exact .inr (by simp only [neg]; rw [← e])
    | frac q hq => cases h
  · rintro ⟨n, h | h⟩ <;> subst h <;> rfl


theorem rat_negOne_pow (k : Nat) : (-1 : Rat) ^ k = if k % 2 = 0 then 1 else -1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Rat.pow_succ, ih]
    by_cases h : k % 2 = 0
    · have h' : ¬ (k + 1) % 2 = 0 := by omega
      simp only [h, h', ↓reduceIte, Rat.one_mul]
    · have h' : (k + 1) % 2 = 0 := by omega
      simp only [h, h', ↓reduceIte, Rat.mul_neg, Rat.mul_one, Rat.neg_neg]

theorem rat_zero_pow (k : Nat) : (0 : Rat) ^ k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp
  | succ k => rw [Rat.pow_succ, Rat.mul_zero]; simp

theorem rat_one_pow (k : Nat) : (1 : Rat) ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Rat.pow_succ, ih, Rat.mul_one]

theorem rat_inv_one : (1 : Rat)⁻¹ = 1 := Rat.inv_eq_of_mul_eq_one (Rat.mul_one 1)

theorem rat_inv_negOne : (-1 : Rat)⁻¹ = -1 :=
  Rat.inv_eq_of_mul_eq_one (by rw [Rat.mul_neg, Rat.mul_one, Rat.neg_neg])

/-- `powInt` is `powIntExact`: its cases 0, 1 and -1 are their powers. -/
theorem powInt_eq (a : Rat) (n : Int) : powInt a n = powIntExact a n := by
  unfold powInt powIntExact
  apply toQ_inj
  rw [toQ_ofQ]
  by_cases h0 : a = 0
  · subst h0
    simp only [↓reduceIte, toQ, rat_zero_pow]
    by_cases hn : n = 0
    · subst hn; simp
    · by_cases hp : 0 ≤ n
      · have : ¬ n.toNat = 0 := by omega
        simp [hn, hp, this]
      · have : ¬ (-n).toNat = 0 := by omega
        simp [hn, hp, this]
  by_cases h1 : a = 1
  · subst h1
    simp only [h0, ↓reduceIte, toQ, rat_one_pow]
    split <;> simp [rat_inv_one]
  by_cases hm : a = -1
  · subst hm
    simp only [h0, h1, ↓reduceIte, toQ, rat_negOne_pow]
    by_cases hp : 0 ≤ n
    · by_cases he : n % 2 = 0
      · have : n.toNat % 2 = 0 := by omega
        simp [hp, he, this]
      · have : ¬ n.toNat % 2 = 0 := by omega
        simp [hp, he, this]
    · by_cases he : n % 2 = 0
      · have : (-n).toNat % 2 = 0 := by omega
        simp [hp, he, this, rat_inv_one]
      · have : ¬ (-n).toNat % 2 = 0 := by omega
        simp [hp, he, this, rat_inv_negOne]
  simp only [h0, h1, hm, ↓reduceIte, toQ_ofQ]
theorem pow_nat (x : MathVal) (n : Nat) : pow x (.int n) = ofQ (x.toQ ^ n) := by
  simp [pow, powInt_eq, powIntExact]

theorem pow_zero (x : MathVal) : pow x (.int (0 : Nat)) = .int 1 := by
  rw [pow_nat]
  apply toQ_inj
  simp [toQ_ofQ]

theorem pow_succ (x : MathVal) (n : Nat) : pow x (.int ((n + 1 : Nat) : Int)) = mul (pow x (.int n)) x := by
  rw [pow_nat, pow_nat]
  apply toQ_inj
  simp [toQ_ofQ, Rat.pow_succ]

/-- The floor of a quotient of integers, over ℚ: Lean's `Int` division rounds toward -∞ for a positive divisor. -/
theorem rat_floor_div_int (a b : Int) (hb : 0 < b) : ((a : Rat) / (b : Rat)).floor = a / b := by
  have hb' : (0 : Rat) < (b : Rat) := Rat.intCast_lt_intCast.2 hb
  have hm := Int.emod_add_mul_ediv a b
  have h0 := Int.emod_nonneg a (Int.ne_of_gt hb)
  have h1 := Int.emod_lt_of_pos a hb
  apply Int.le_antisymm
  · have : ((a : Rat) / (b : Rat)).floor < a / b + 1 := by
      rw [Rat.floor_lt_iff, Rat.div_lt_iff hb', ← Rat.intCast_mul, Rat.intCast_lt_intCast]
      have : (a / b + 1) * b = b * (a / b) + b := by rw [Int.add_mul, Int.mul_comm]; simp
      omega
    omega
  · rw [Rat.le_floor_iff]
    apply Rat.not_lt.1
    rw [Rat.div_lt_iff hb', ← Rat.intCast_mul, Rat.intCast_lt_intCast]
    have : (a / b) * b = b * (a / b) := Int.mul_comm _ _
    omega

/-- floor(a / b) of integers, b positive, as a mathematical value: the integer `a / b`. -/
theorem floor_div_int (a b : Int) (hb : 0 < b) : floor (div (.int a) (.int b)) = .int (a / b) := by
  have h := toQ_floor (div (.int a) (.int b))
  have hd : (div (.int a) (.int b)).toQ = (a : Rat) / (b : Rat) := by
    show (ofQ _).toQ = _
    rw [toQ_ofQ]; rfl
  rw [hd, rat_floor_div_int a b hb] at h
  exact toQ_inj h

end Engine.Model.MathVal

/-! The same, as `Model.Laws` states them of `Impl`. -/

namespace Engine.Impl
open Ecma Engine.Model

theorem add_assoc : ∀ a b c, Impl.add (Impl.add a b) c = Impl.add a (Impl.add b c) := MathVal.add_assoc
theorem add_comm : ∀ a b, Impl.add a b = Impl.add b a := MathVal.add_comm
theorem add_zero : ∀ a, Impl.add a (Impl.ofNat 0) = a := MathVal.add_zero
theorem add_neg : ∀ a, Impl.add a (Impl.neg a) = Impl.ofNat 0 := MathVal.add_neg
theorem sub_def : ∀ a b, Impl.sub a b = Impl.add a (Impl.neg b) := fun _ _ => rfl
theorem mul_assoc : ∀ a b c, Impl.mul (Impl.mul a b) c = Impl.mul a (Impl.mul b c) := MathVal.mul_assoc
theorem mul_comm : ∀ a b, Impl.mul a b = Impl.mul b a := MathVal.mul_comm
theorem mul_one : ∀ a, Impl.mul a (Impl.ofNat 1) = a := MathVal.mul_one
theorem mul_add : ∀ a b c, Impl.mul a (Impl.add b c) = Impl.add (Impl.mul a b) (Impl.mul a c) := MathVal.mul_add
theorem div_mul : ∀ a b, b ≠ Impl.ofNat 0 → Impl.mul (Impl.div a b) b = a := MathVal.div_mul
theorem zero_ne_one : Impl.ofNat 0 ≠ Impl.ofNat 1 := MathVal.zero_ne_one
theorem lt_irrefl : ∀ a, Impl.lt a a = false := MathVal.lt_irrefl
theorem lt_trans : ∀ a b c, Impl.lt a b = true → Impl.lt b c = true → Impl.lt a c = true := MathVal.lt_trans
theorem lt_total : ∀ a b, Impl.lt a b = true ∨ a = b ∨ Impl.lt b a = true := MathVal.lt_total
theorem add_lt_add : ∀ a b c, Impl.lt a b = true → Impl.lt (Impl.add a c) (Impl.add b c) = true := MathVal.add_lt_add
theorem mul_pos : ∀ a b, Impl.lt (Impl.ofNat 0) a = true → Impl.lt (Impl.ofNat 0) b = true →
    Impl.lt (Impl.ofNat 0) (Impl.mul a b) = true := MathVal.mul_pos
theorem eq_iff : ∀ a b, Impl.eq a b = true ↔ a = b := MathVal.eq_iff
theorem ofNat_add : ∀ m n, Impl.ofNat (m + n) = Impl.add (Impl.ofNat m) (Impl.ofNat n) := MathVal.ofNat_add
theorem pow_zero : ∀ x, Impl.pow x (Impl.ofNat 0) = Impl.ofNat 1 := MathVal.pow_zero
theorem pow_succ : ∀ x n, Impl.pow x (Impl.ofNat (n + 1)) = Impl.mul (Impl.pow x (Impl.ofNat n)) x := MathVal.pow_succ
theorem floor_isInt : ∀ x, Impl.isInt (Impl.floor x) = true := MathVal.floor_isInt
theorem floor_le : ∀ x, Impl.lt x (Impl.floor x) = false := MathVal.floor_le
theorem lt_floor_add_one : ∀ x, Impl.lt x (Impl.add (Impl.floor x) (Impl.ofNat 1)) = true := MathVal.lt_floor_add_one
theorem isInt_iff : ∀ x, Impl.isInt x = true ↔ ∃ n, x = Impl.ofNat n ∨ x = Impl.neg (Impl.ofNat n) := MathVal.isInt_iff

/-- §6.1.6.2: a BigInt is an integer, and is its value. -/
theorem bigVal_bigOf : ∀ x, Impl.isInt x = true → Impl.bigVal (Impl.bigOf x) = x := by
  intro x h
  cases x with
  | int i => rfl
  | frac q hq => cases h
theorem bigVal_isInt : ∀ b, Impl.isInt (Impl.bigVal b) = true := fun _ => rfl
theorem bigVal_inj : ∀ a b, Impl.bigVal a = Impl.bigVal b → a = b := fun _ _ h => MathVal.int.inj h

end Engine.Impl
