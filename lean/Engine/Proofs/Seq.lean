module

public import Engine.Proofs.Str

@[expose] public section

/-!
# The laws of Lists at the engine's model

A List is an array (§6.2.2); an index is a mathematical value, and only a non-negative integer below the length
has an element.
-/

namespace Engine.Model.MathVal

/-- A mathematical value is a non-negative integer, a negative one, or not an integer. -/
theorem idxCases {P : MathVal → Prop} (nat : ∀ k : Nat, P (.int k)) (negi : ∀ j : Int, j < 0 → P (.int j))
    (fr : ∀ q h, P (.frac q h)) : ∀ i, P i := by
  intro i
  cases i with
  | int j =>
    by_cases hj : 0 ≤ j
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
      exact nat k
    · exact negi j (by omega)
  | frac q h => exact fr q h

theorem idx_negi {j : Int} (h : j < 0) : idx (.int j) = none := by
  simp only [idx]
  rw [if_neg (by omega)]

/-- A sum with an integer that is an integer is of an integer. -/
theorem add_int_eq {a : MathVal} {n m : Int} (h : add a (.int n) = .int m) : a = .int (m - n) := by
  have : a = .int (m + -n) := sub_int_eq (n := -n) (by simpa [neg] using h)
  rw [this]
  congr 1

theorem idx_frac_add (q : Rat) (h : q.den ≠ 1) (n : Int) : idx (add (.frac q h) (.int n)) = none := by
  cases hi : idx (add (.frac q h) (.int n)) with
  | none => rfl
  | some k => cases add_int_eq (idx_some hi)

theorem eq_frac_int (q : Rat) (h : q.den ≠ 1) (n : Int) : eq (.frac q h) (.int n) = false := by
  cases he : eq (.frac q h) (.int n) with
  | false => rfl
  | true => cases (eq_iff _ _).1 he

theorem eq_int (a b : Int) : eq (.int a) (.int b) = decide (a = b) := by
  unfold eq
  by_cases h : a = b <;> simp [h]

theorem lt_int (a b : Int) : lt (.int a) (.int b) = decide (a < b) := rfl

end Engine.Model.MathVal

namespace Engine.Impl
open Ecma Engine.Model

variable {α β : Type}

theorem seqGet_def (xs : Array α) (i : MathVal) : Impl.seqGet xs i = (MathVal.idx i).bind fun k => xs[k]? := rfl

theorem seqGet_nat (xs : Array α) (k : Nat) : Impl.seqGet xs (.int k) = xs[k]? := by
  rw [seqGet_def, MathVal.idx_nat]; rfl

theorem seqGet_negi (xs : Array α) {j : Int} (h : j < 0) : Impl.seqGet xs (.int j) = none := by
  rw [seqGet_def, MathVal.idx_negi h]; rfl

theorem seqGet_frac (xs : Array α) (q : Rat) (h : q.den ≠ 1) : Impl.seqGet xs (.frac q h) = none := rfl

theorem seqGet_none_of_idx (xs : Array α) {i : MathVal} (h : MathVal.idx i = none) : Impl.seqGet xs i = none := by
  rw [seqGet_def, h]; rfl

theorem seqLen_nat : ∀ (xs : Array α), ∃ n, Impl.seqLen xs = Impl.ofNat n := fun xs => ⟨xs.size, rfl⟩

/-- An index with an element is a natural number below the size. -/
theorem seqGet_idx {xs : Array α} {i : MathVal} {a : α} (h : Impl.seqGet xs i = some a) :
    ∃ k : Nat, i = .int k ∧ k < xs.size ∧ xs[k]? = some a := by
  revert h
  refine MathVal.idxCases (P := fun i => Impl.seqGet xs i = some a → ∃ k : Nat, i = .int k ∧ k < xs.size ∧ xs[k]? = some a)
    ?_ ?_ ?_ i
  · intro k h
    rw [seqGet_nat] at h
    exact ⟨k, rfl, (Array.getElem?_eq_some_iff.1 h).1, h⟩
  · intro j hj h
    rw [seqGet_negi xs hj] at h
    cases h
  · intro q hq h
    cases h

theorem seqGet_some : ∀ (xs : Array α) (i : MathVal) (a : α), Impl.seqGet xs i = some a →
    ∃ k, i = Impl.ofNat k ∧ Impl.lt i (Impl.seqLen xs) = true := by
  intro xs i a h
  obtain ⟨k, rfl, hk, _⟩ := seqGet_idx h
  refine ⟨k, rfl, ?_⟩
  show MathVal.lt (.int k) (.int xs.size) = true
  rw [MathVal.lt_nat]
  exact decide_eq_true hk

theorem lt_size {k : Nat} {xs : Array α} (h : Impl.lt (Impl.ofNat k) (Impl.seqLen xs) = true) : k < xs.size := by
  have : MathVal.lt (.int k) (.int xs.size) = true := h
  rw [MathVal.lt_nat] at this
  exact of_decide_eq_true this

theorem seqGet_lt : ∀ (xs : Array α) (k : Nat), Impl.lt (Impl.ofNat k) (Impl.seqLen xs) = true →
    (Impl.seqGet xs (Impl.ofNat k)).isSome = true := by
  intro xs k h
  have hk := lt_size h
  show (Impl.seqGet xs (.int k)).isSome = true
  rw [seqGet_nat]
  simp [hk]

theorem seq_ext : ∀ (xs ys : Array α), (∀ i, Impl.seqGet xs i = Impl.seqGet ys i) → xs = ys := by
  intro xs ys h
  apply Array.ext_getElem?
  intro k
  have := h (.int k)
  rwa [seqGet_nat, seqGet_nat] at this

theorem seqLen_nil : Impl.seqLen (Impl.seqNil (α := α)) = Impl.ofNat 0 := rfl

theorem seqGet_nil : ∀ i, Impl.seqGet (Impl.seqNil (α := α)) i = none := by
  intro i
  show ((MathVal.idx i).bind fun k => (#[] : Array α)[k]?) = none
  cases MathVal.idx i <;> simp

theorem seqLen_push : ∀ (xs : Array α) (a : α),
    Impl.seqLen (Impl.seqPush xs a) = Impl.add (Impl.seqLen xs) (Impl.ofNat 1) := by
  intro xs a
  show MathVal.int ((xs.push a).size : Nat) = MathVal.add (.int xs.size) (.int (1 : Nat))
  simp [MathVal.add]

theorem seqGet_push : ∀ (xs : Array α) (a : α) (i : MathVal),
    Impl.seqGet (Impl.seqPush xs a) i = if Impl.eq i (Impl.seqLen xs) then some a else Impl.seqGet xs i := by
  intro xs a i
  show Impl.seqGet (xs.push a) i = if MathVal.eq i (.int xs.size) then some a else Impl.seqGet xs i
  refine MathVal.idxCases (P := fun i => Impl.seqGet (xs.push a) i =
    if MathVal.eq i (.int xs.size) then some a else Impl.seqGet xs i) ?_ ?_ ?_ i
  · intro k
    rw [seqGet_nat, seqGet_nat, MathVal.eq_int, Array.getElem?_push]
    by_cases h : k = xs.size
    · simp [h]
    · have : (k : Int) ≠ xs.size := by omega
      simp [h, this]
  · intro j hj
    rw [seqGet_negi _ hj, seqGet_negi _ hj, MathVal.eq_int]
    have : j ≠ (xs.size : Int) := by omega
    simp [this]
  · intro q hq
    rw [MathVal.eq_frac_int]
    rfl

theorem seqLen_cons : ∀ (a : α) (xs : Array α),
    Impl.seqLen (Impl.seqCons a xs) = Impl.add (Impl.seqLen xs) (Impl.ofNat 1) := by
  intro a xs
  show MathVal.int ((#[a] ++ xs).size : Nat) = MathVal.add (.int xs.size) (.int (1 : Nat))
  simp only [MathVal.add]
  congr 1
  simp
  omega

theorem seqGet_cons : ∀ (a : α) (xs : Array α) (i : MathVal), Impl.seqGet (Impl.seqCons a xs) i =
    if Impl.eq i (Impl.ofNat 0) then some a else Impl.seqGet xs (Impl.sub i (Impl.ofNat 1)) := by
  intro a xs i
  show Impl.seqGet (#[a] ++ xs) i = if MathVal.eq i (.int (0 : Nat)) then some a
    else Impl.seqGet xs (MathVal.add i (MathVal.neg (.int (1 : Nat))))
  refine MathVal.idxCases (P := fun i => Impl.seqGet (#[a] ++ xs) i = if MathVal.eq i (.int (0 : Nat)) then some a
    else Impl.seqGet xs (MathVal.add i (MathVal.neg (.int (1 : Nat))))) ?_ ?_ ?_ i
  · intro k
    rw [seqGet_nat, MathVal.eq_int]
    cases k with
    | zero =>
      rw [Array.getElem?_append_left (by simp : 0 < #[a].size)]
      simp
    | succ n =>
      have e : MathVal.add (.int ((n + 1 : Nat) : Int)) (MathVal.neg (.int (1 : Nat))) = .int (n : Nat) := by
        simp only [MathVal.add, MathVal.neg]
        congr 1
        omega
      rw [e, seqGet_nat, Array.getElem?_append_right (by simp : #[a].size ≤ n + 1)]
      have : (n : Int) + 1 ≠ 0 := by omega
      simp [this]
  · intro j hj
    rw [seqGet_negi _ hj, MathVal.eq_int]
    have e : MathVal.add (.int j) (MathVal.neg (.int (1 : Nat))) = .int (j + -1) := rfl
    rw [e, seqGet_negi _ (by omega)]
    have : j ≠ 0 := by omega
    simp [this]
  · intro q hq
    rw [MathVal.eq_frac_int]
    have e : MathVal.neg (.int (1 : Nat)) = .int (-1) := rfl
    rw [e, seqGet_none_of_idx xs (MathVal.idx_frac_add q hq _)]
    rfl

theorem seqLen_set : ∀ (xs : Array α) (i : MathVal) (a : α), Impl.seqLen (Impl.seqSet xs i a) = Impl.seqLen xs := by
  intro xs i a
  show MathVal.int ((match MathVal.idx i with
    | some k => xs.setIfInBounds k a
    | none => xs).size : Nat) = MathVal.int xs.size
  cases MathVal.idx i <;> simp

theorem seqSet_nat (xs : Array α) (k : Nat) (a : α) : Impl.seqSet xs (.int k) a = xs.setIfInBounds k a := by
  show (match MathVal.idx (.int k) with
    | some k => xs.setIfInBounds k a
    | none => xs) = _
  rw [MathVal.idx_nat]

theorem seqSet_none (xs : Array α) {i : MathVal} (h : MathVal.idx i = none) (a : α) : Impl.seqSet xs i a = xs := by
  show (match MathVal.idx i with
    | some k => xs.setIfInBounds k a
    | none => xs) = _
  rw [h]

theorem seqGet_set : ∀ (xs : Array α) (i : MathVal) (a : α) (j : MathVal), Impl.seqGet (Impl.seqSet xs i a) j =
    if Impl.eq j i && (Impl.seqGet xs i).isSome then some a else Impl.seqGet xs j := by
  intro xs i a j
  show Impl.seqGet (Impl.seqSet xs i a) j = if MathVal.eq j i && (Impl.seqGet xs i).isSome then some a else Impl.seqGet xs j
  refine MathVal.idxCases (P := fun i => Impl.seqGet (Impl.seqSet xs i a) j =
    if MathVal.eq j i && (Impl.seqGet xs i).isSome then some a else Impl.seqGet xs j) ?_ ?_ ?_ i
  · intro k
    rw [seqSet_nat, seqGet_nat]
    refine MathVal.idxCases (P := fun j => Impl.seqGet (xs.setIfInBounds k a) j =
      if MathVal.eq j (.int k) && (xs[k]?).isSome then some a else Impl.seqGet xs j) ?_ ?_ ?_ j
    · intro m
      rw [seqGet_nat, seqGet_nat, MathVal.eq_int, Array.getElem?_setIfInBounds]
      by_cases hm : k = m
      · subst hm
        by_cases hk : k < xs.size <;> simp [hk]
      · have : (m : Int) ≠ k := by omega
        simp [hm, this]
    · intro m hm
      rw [seqGet_negi _ hm, seqGet_negi _ hm, MathVal.eq_int]
      have : m ≠ (k : Int) := by omega
      simp [this]
    · intro q hq
      rw [MathVal.eq_frac_int]
      rfl
  · intro m hm
    rw [seqSet_none xs (MathVal.idx_negi hm), seqGet_negi xs hm]
    simp
  · intro q hq
    rw [seqSet_none xs rfl, seqGet_frac]
    simp

theorem seqLen_concat : ∀ (xs ys : Array α),
    Impl.seqLen (Impl.seqConcat xs ys) = Impl.add (Impl.seqLen xs) (Impl.seqLen ys) := by
  intro xs ys
  show MathVal.int ((xs ++ ys).size : Nat) = MathVal.add (.int xs.size) (.int ys.size)
  simp [MathVal.add]

theorem seqGet_concat : ∀ (xs ys : Array α) (i : MathVal), Impl.seqGet (Impl.seqConcat xs ys) i =
    if Impl.lt i (Impl.seqLen xs) then Impl.seqGet xs i else Impl.seqGet ys (Impl.sub i (Impl.seqLen xs)) := by
  intro xs ys i
  show Impl.seqGet (xs ++ ys) i = if MathVal.lt i (.int xs.size) then Impl.seqGet xs i
    else Impl.seqGet ys (MathVal.add i (MathVal.neg (.int xs.size)))
  refine MathVal.idxCases (P := fun i => Impl.seqGet (xs ++ ys) i = if MathVal.lt i (.int xs.size) then Impl.seqGet xs i
    else Impl.seqGet ys (MathVal.add i (MathVal.neg (.int xs.size)))) ?_ ?_ ?_ i
  · intro k
    rw [seqGet_nat, seqGet_nat, MathVal.lt_nat]
    by_cases hk : k < xs.size
    · simp [hk, Array.getElem?_append_left hk]
    · have e : MathVal.add (.int k) (MathVal.neg (.int xs.size)) = .int ((k - xs.size : Nat) : Int) := by
        simp only [MathVal.add, MathVal.neg]
        congr 1
        omega
      rw [e, seqGet_nat]
      simp [hk, Array.getElem?_append_right (Nat.le_of_not_lt hk)]
  · intro j hj
    rw [seqGet_negi _ hj, seqGet_negi _ hj, MathVal.lt_int]
    have : j < (xs.size : Int) := by omega
    simp [this]
  · intro q hq
    have e : MathVal.neg (.int (xs.size : Nat)) = .int (-(xs.size : Int)) := rfl
    rw [e, seqGet_none_of_idx ys (MathVal.idx_frac_add q hq _), seqGet_frac, seqGet_frac]
    simp

theorem seqRemove_nat (xs : Array α) (k : Nat) : Impl.seqRemove xs (.int k) = xs.eraseIdxIfInBounds k := by
  show (match MathVal.idx (.int k) with
    | some k => xs.eraseIdxIfInBounds k
    | none => xs) = _
  rw [MathVal.idx_nat]

theorem seqRemove_idx_none (xs : Array α) {i : MathVal} (h : MathVal.idx i = none) : Impl.seqRemove xs i = xs := by
  show (match MathVal.idx i with
    | some k => xs.eraseIdxIfInBounds k
    | none => xs) = _
  rw [h]

theorem seqLen_remove : ∀ (xs : Array α) (i : MathVal), (Impl.seqGet xs i).isSome = true →
    Impl.seqLen (Impl.seqRemove xs i) = Impl.sub (Impl.seqLen xs) (Impl.ofNat 1) := by
  intro xs i h
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨k, rfl, hk, _⟩ := seqGet_idx ha
  show MathVal.int ((Impl.seqRemove xs (.int k)).size : Nat) = MathVal.add (.int xs.size) (MathVal.neg (.int (1 : Nat)))
  rw [seqRemove_nat]
  simp only [MathVal.add, MathVal.neg, Array.eraseIdxIfInBounds_eq, hk, dite_true, Array.size_eraseIdx]
  congr 1
  omega

theorem seqGet_remove : ∀ (xs : Array α) (i j : MathVal), (Impl.seqGet xs i).isSome = true →
    Impl.seqGet (Impl.seqRemove xs i) j =
      if Impl.lt j i then Impl.seqGet xs j else Impl.seqGet xs (Impl.add j (Impl.ofNat 1)) := by
  intro xs i j h
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨k, rfl, hk, _⟩ := seqGet_idx ha
  show Impl.seqGet (Impl.seqRemove xs (.int k)) j =
    if MathVal.lt j (.int k) then Impl.seqGet xs j else Impl.seqGet xs (MathVal.add j (.int (1 : Nat)))
  rw [seqRemove_nat]
  refine MathVal.idxCases (P := fun j => Impl.seqGet (xs.eraseIdxIfInBounds k) j =
    if MathVal.lt j (.int k) then Impl.seqGet xs j else Impl.seqGet xs (MathVal.add j (.int (1 : Nat)))) ?_ ?_ ?_ j
  · intro m
    have e : MathVal.add (.int m) (.int (1 : Nat)) = .int ((m + 1 : Nat) : Int) := rfl
    rw [e, seqGet_nat, seqGet_nat, seqGet_nat, MathVal.lt_nat]
    simp only [Array.eraseIdxIfInBounds_eq, hk, dite_true, Array.getElem?_eraseIdx]
    by_cases hm : m < k <;> simp [hm]
  · intro m hm
    rw [seqGet_negi _ hm, seqGet_negi _ hm, MathVal.lt_int]
    have : m < (k : Int) := by omega
    simp [this]
  · intro q hq
    rw [seqGet_none_of_idx xs (MathVal.idx_frac_add q hq _), seqGet_frac, seqGet_frac]
    simp

theorem seqRemove_none : ∀ (xs : Array α) (i : MathVal), Impl.seqGet xs i = none → Impl.seqRemove xs i = xs := by
  intro xs i
  refine MathVal.idxCases (P := fun i => Impl.seqGet xs i = none → Impl.seqRemove xs i = xs) ?_ ?_ ?_ i
  · intro k h
    rw [seqGet_nat] at h
    have hk : ¬ k < xs.size := by
      intro hk
      rw [Array.getElem?_eq_getElem hk] at h
      cases h
    rw [seqRemove_nat]
    simp [Array.eraseIdxIfInBounds_eq, hk]
  · intro j hj _
    exact seqRemove_idx_none xs (MathVal.idx_negi hj)
  · intro q hq _
    exact seqRemove_idx_none xs rfl

theorem seqLen_repeat : ∀ (k : Nat) (a : α), Impl.seqLen (Impl.seqRepeat (Impl.ofNat k) a) = Impl.ofNat k := by
  intro k a
  show MathVal.int ((match MathVal.idx (.int k) with
    | some k => Array.replicate k a
    | none => #[]).size : Nat) = .int k
  rw [MathVal.idx_nat]
  simp

theorem seqGet_repeat : ∀ (k : Nat) (a : α) (i : MathVal) (x : α),
    Impl.seqGet (Impl.seqRepeat (Impl.ofNat k) a) i = some x → x = a := by
  intro k a i x h
  have h' : Impl.seqGet (Array.replicate k a) i = some x := by
    have : Impl.seqRepeat (Impl.ofNat k) a = Array.replicate k a := by
      show (match MathVal.idx (.int k) with
        | some k => Array.replicate k a
        | none => #[]) = Array.replicate k a
      rw [MathVal.idx_nat]
    rwa [this] at h
  obtain ⟨j, -, -, hj⟩ := seqGet_idx h'
  simp only [Array.getElem?_replicate] at hj
  split at hj <;> simp_all

theorem seqFoldl_nil : ∀ (f : β → α → β) (b : β), Impl.seqFoldl f b (Impl.seqNil (α := α)) = b := by
  intro f b
  show Array.foldl f b (#[] : Array α) = b
  simp

theorem seqFoldl_push : ∀ (f : β → α → β) (b : β) (xs : Array α) (a : α),
    Impl.seqFoldl f b (Impl.seqPush xs a) = f (Impl.seqFoldl f b xs) a := by
  intro f b xs a
  show Array.foldl f b (xs.push a) = f (Array.foldl f b xs) a
  simp

end Engine.Impl
