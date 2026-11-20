module

public import Engine.Model.CharSetData
public import Engine.Proofs.UnicodeLemmas

@[expose] public section

/-!
# Correctness of binary search, normalized range operations, and `WMap` string folds
-/

namespace Engine.Model

/-! ## Bisection (`Unicode.lastLE`) correctness -/

theorem bisect_range'_inv {α : Type} (key : α → Nat) (a : Array α) (c : Nat)
    (hsort : ∀ i j (hi : i < a.size) (hj : j < a.size), i ≤ j → key a[i] ≤ key a[j]) :
    ∀ (k s lo : Nat),
      lo ≤ a.size →
      (∀ i (hi : i < a.size), i < lo → key a[i] ≤ c) →
      (∀ i (hi : i < a.size), lo + 2 ^ k - 1 ≤ i → c < key a[i]) →
      let res := (List.range' s k).foldl (_root_.Unicode.bisectRound key a c (s + k)) lo
      res ≤ a.size ∧ (∀ i (hi : i < a.size), i < res → key a[i] ≤ c) ∧
        (∀ i (hi : i < a.size), res ≤ i → c < key a[i]) := by
  intro k
  induction k with
  | zero =>
    intro s lo hle hlo hhi
    simpa [List.range', List.foldl] using ⟨hle, hlo, fun i hi hlt => hhi i hi (by simpa using hlt)⟩
  | succ k ih =>
    intro s lo hle hlo hhi
    rw [List.range'_succ, List.foldl_cons]
    have hinv :
        let lo' := _root_.Unicode.bisectRound key a c (s + (k + 1)) lo s
        lo' ≤ a.size ∧ (∀ i (hi : i < a.size), i < lo' → key a[i] ≤ c) ∧
          (∀ i (hi : i < a.size), lo' + 2 ^ k - 1 ≤ i → c < key a[i]) := by
      unfold _root_.Unicode.bisectRound
      have hpow : s + (k + 1) - 1 - s = k := by omega
      simp only [hpow]
      let half := 2 ^ k
      have hhalfPos : 1 ≤ half := Nat.one_le_two_pow
      have h2 : 2 ^ (k + 1) = 2 * half := by rw [Nat.pow_succ]; omega
      cases hget : a[lo + half - 1]? with
      | none =>
        have hge : a.size ≤ lo + half - 1 :=
          Classical.byContradiction fun hlt => by
            have hlt' : lo + half - 1 < a.size := Nat.lt_of_not_le hlt
            rw [Array.getElem?_eq_getElem hlt'] at hget; cases hget
        exact ⟨hle, hlo, fun i hi hlt => by dsimp only [half] at hge; dsimp only at hlt; omega⟩
      | some r =>
        have hrIdx : lo + half - 1 < a.size := (Array.getElem?_eq_some_iff.1 hget).1
        have hrEq : a[lo + half - 1] = r := (Array.getElem?_eq_some_iff.1 hget).2
        by_cases hk : key r ≤ c
        · simp only [hk, ↓reduceIte]
          refine ⟨by omega, ?_, ?_⟩
          · intro i hiSize hi
            have := hsort i (lo + half - 1) hiSize hrIdx (by omega)
            rw [hrEq] at this; omega
          · intro i hi hlt
            exact hhi i hi (by omega)
        · simp only [hk, ↓reduceIte]
          refine ⟨hle, hlo, ?_⟩
          intro i hlt hiGe
          have := hsort (lo + half - 1) i hrIdx hlt (by omega)
          rw [hrEq] at this; omega
    have hr := ih (s + 1) _ hinv.1 hinv.2.1 hinv.2.2
    have hadd : s + 1 + k = s + (k + 1) := by omega
    simpa [hadd] using hr

theorem lastLE_spec {α : Type} (key : α → Nat) (a : Array α) (c : Nat)
    (hsort : ∀ i j (hi : i < a.size) (hj : j < a.size), i ≤ j → key a[i] ≤ key a[j]) :
    (_root_.Unicode.lastLE key a c = none → ∀ j (hj : j < a.size), c < key a[j]) ∧
      (∀ r, _root_.Unicode.lastLE key a c = some r →
        ∃ idx, idx < a.size ∧ a[idx]? = some r ∧ key r ≤ c ∧ ∀ j (hj : j < a.size), key a[j] ≤ c → j ≤ idx) := by
  unfold _root_.Unicode.lastLE _root_.Unicode.bisect
  simp only [List.range_eq_range']
  let d := a.size.log2 + 1
  have hltPow : a.size < 2 ^ d := Nat.lt_log2_self
  have hb := bisect_range'_inv key a c hsort d 0 0 (Nat.zero_le _) (fun _ _ h => absurd h (Nat.not_lt_zero _))
    (fun i hi hlt => by omega)
  simp only [Nat.zero_add] at hb
  let n := (List.range' 0 d).foldl (_root_.Unicode.bisectRound key a c d) 0
  obtain ⟨hnLe, hLtN, hGeN⟩ := hb
  constructor
  · intro hnone j hj
    by_cases hn0 : n = 0
    · exact hGeN j hj (by omega)
    · exfalso
      have hnone' : (if n = 0 then none else a[n - 1]?) = none := hnone
      simp only [hn0, ↓reduceIte] at hnone'
      have hidx : n - 1 < a.size := by omega
      rw [Array.getElem?_eq_getElem hidx] at hnone'; cases hnone'
  · intro r hr
    by_cases hn0 : n = 0
    · have hr' : (if n = 0 then none else a[n - 1]?) = some r := hr
      simp [hn0] at hr'
    · have hr' : (if n = 0 then none else a[n - 1]?) = some r := hr
      simp only [hn0, ↓reduceIte] at hr'
      have hidx : n - 1 < a.size := by omega
      have haEq : a[n - 1] = r := by rw [Array.getElem?_eq_getElem hidx] at hr'; cases hr'; rfl
      refine ⟨n - 1, hidx, by rw [Array.getElem?_eq_getElem hidx, haEq], ?_, ?_⟩
      · have := hLtN (n - 1) hidx (by omega); rw [haEq] at this; exact this
      · intro j hj hjk
        exact Classical.byContradiction fun hnot => by
          have := hGeN j hj (by omega); omega

theorem lookupSortedA_iff {β : Type} (a : Array (Nat × β))
    (hsort : ∀ i j (hi : i < a.size) (hj : j < a.size), i < j → a[i].1 < a[j].1) (c : Nat) (b : β) :
    _root_.Unicode.lookupSortedA a c = some b ↔ (c, b) ∈ a.toList := by
  have hle : ∀ i j (hi : i < a.size) (hj : j < a.size), i ≤ j → a[i].1 ≤ a[j].1 := fun i j hi hj hij =>
    (Nat.lt_or_eq_of_le hij).elim (fun h => Nat.le_of_lt (hsort i j hi hj h)) (fun h => h ▸ Nat.le_refl _)
  obtain ⟨hnone, hsome⟩ := lastLE_spec Prod.fst a c hle
  unfold _root_.Unicode.lookupSortedA
  constructor
  · intro h
    cases hl : _root_.Unicode.lastLE Prod.fst a c with
    | none => simp [hl] at h
    | some p =>
      rw [hl] at h; dsimp only at h
      split at h
      · cases h; rename_i hc
        obtain ⟨idx, hidx, heq, _⟩ := hsome p hl
        rw [Array.getElem?_eq_getElem hidx] at heq; cases heq
        exact hc ▸ Array.mem_toList_iff.2 (Array.getElem_mem hidx)
      · cases h
  · intro hm
    obtain ⟨j, hj, hjEq⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hm)
    cases hl : _root_.Unicode.lastLE Prod.fst a c with
    | none => have := hnone hl j hj; rw [hjEq] at this; exact absurd this (Nat.lt_irrefl _)
    | some p =>
      obtain ⟨idx, hidx, hidxEq, hpLe, hmax⟩ := hsome p hl
      rw [Array.getElem?_eq_getElem hidx] at hidxEq; cases hidxEq
      have hleJ := hmax j hj (by simp [hjEq])
      have hEqIdx : j = idx := Classical.byContradiction fun hne => by
        have := hsort j idx hj hidx (Nat.lt_of_le_of_ne hleJ hne)
        rw [hjEq] at this; omega
      subst hEqIdx; rw [hjEq]; simp

/-! ## Range lists and `inRangesA` -/

def MemRanges (rs : List (Nat × Nat)) (c : Nat) : Prop :=
  ∃ r ∈ rs, r.1 ≤ c ∧ c ≤ r.2

@[simp] theorem memRanges_nil (c : Nat) : MemRanges [] c ↔ False := by simp [MemRanges]

@[simp] theorem memRanges_cons (a b : Nat) (r : List (Nat × Nat)) (c : Nat) :
    MemRanges ((a, b) :: r) c ↔ (a ≤ c ∧ c ≤ b) ∨ MemRanges r c := by simp [MemRanges]

theorem rangeListOk_tail {m : Nat} {x : Nat × Nat} {r : List (Nat × Nat)}
    (h : rangeListOk m (x :: r) = true) : rangeListOk (x.2 + 2) r = true := by
  rcases x with ⟨lo, hi⟩; simp only [rangeListOk, Bool.and_eq_true] at h; exact h.2

theorem rangeListOk_mono {m1 m2 : Nat} {rs : List (Nat × Nat)} (hle : m1 ≤ m2)
    (h : rangeListOk m2 rs = true) : rangeListOk m1 rs = true := by
  cases rs with
  | nil => rfl
  | cons x r =>
    rcases x with ⟨lo, hi⟩
    simp only [rangeListOk, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨⟨by omega, h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem rangeListOk_head_le {m : Nat} {rs : List (Nat × Nat)} (h : rangeListOk m rs = true) :
    ∀ x ∈ rs, m ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 ≤ maxCodePoint := by
  induction rs generalizing m with
  | nil => intro _ hx; cases hx
  | cons p r ih =>
    rcases p with ⟨lo, hi⟩
    simp only [rangeListOk, Bool.and_eq_true, decide_eq_true_eq] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
    · have := ih h.2 x hx; omega

theorem rangeListOk_pairwise {m : Nat} {rs : List (Nat × Nat)} (h : rangeListOk m rs = true) :
    rs.Pairwise fun x y => x.2 + 2 ≤ y.1 := by
  induction rs generalizing m with
  | nil => simp
  | cons x r ih =>
    rcases x with ⟨lo, hi⟩
    have ht := rangeListOk_tail h
    exact List.pairwise_cons.2 ⟨fun y hy => (rangeListOk_head_le ht y hy).1, ih ht⟩

theorem memRanges_le_max {m : Nat} {rs : List (Nat × Nat)} (h : rangeListOk m rs = true) {c : Nat}
    (hc : MemRanges rs c) : c ≤ maxCodePoint := by
  obtain ⟨x, hx, _, hx2⟩ := hc
  exact Nat.le_trans hx2 (rangeListOk_head_le h x hx).2.2

theorem inRangesA_iff (rs : Array (Nat × Nat)) (h : rangeListOk 0 rs.toList = true) (c : Nat) :
    _root_.Unicode.inRangesA rs c = true ↔ MemRanges rs.toList c := by
  have hpw := rangeListOk_pairwise h
  have hsort : ∀ i j (hi : i < rs.size) (hj : j < rs.size), i ≤ j → rs[i].1 ≤ rs[j].1 := by
    intro i j hi hj hij
    rcases Nat.lt_or_eq_of_le hij with hlt | rfl
    · have hmem := List.pairwise_iff_getElem.1 hpw i j (by simpa) (by simpa) hlt
      have hbi := rangeListOk_head_le h rs[i] (Array.mem_toList_iff.2 (Array.getElem_mem hi))
      simp only [Array.getElem_toList] at hmem
      omega
    · exact Nat.le_refl _
  obtain ⟨hnone, hsome⟩ := lastLE_spec Prod.fst rs c hsort
  unfold _root_.Unicode.inRangesA
  constructor
  · intro hin
    cases hl : _root_.Unicode.lastLE Prod.fst rs c with
    | none => simp [hl] at hin
    | some p =>
      rw [hl] at hin
      obtain ⟨idx, hidx, heq, hp1, _⟩ := hsome p hl
      rw [Array.getElem?_eq_getElem hidx] at heq; cases heq
      exact ⟨rs[idx], Array.mem_toList_iff.2 (Array.getElem_mem hidx), hp1, of_decide_eq_true hin⟩
  · rintro ⟨⟨lo, hi⟩, hm, h1, h2⟩
    obtain ⟨j, hj, hjEq⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hm)
    cases hl : _root_.Unicode.lastLE Prod.fst rs c with
    | none => have := hnone hl j hj; rw [hjEq] at this; exact absurd h1 (Nat.not_le_of_gt this)
    | some p =>
      obtain ⟨idx, hidx, heq, hp1, hmax⟩ := hsome p hl
      rw [Array.getElem?_eq_getElem hidx] at heq; cases heq
      have hjLe := hmax j hj (by rw [hjEq]; exact h1)
      rcases Nat.lt_or_eq_of_le hjLe with hlt | rfl
      · have := List.pairwise_iff_getElem.1 hpw j idx (by simpa) (by simpa) hlt
        simp only [Array.getElem_toList] at this
        rw [hjEq] at this; omega
      · rw [hjEq] at hp1 ⊢; simpa using decide_eq_true h2

/-! ## Canonical range loops (`unionRanges`, `complRanges`, `diffRanges`, `interRanges`) -/

def RevOk : List (Nat × Nat) → Prop
  | [] => True
  | (lo, hi) :: r => lo ≤ hi ∧ hi ≤ maxCodePoint ∧
    match r with
    | [] => True
    | (_, phi) :: _ => phi + 2 ≤ lo ∧ RevOk r

def revHeadLo : List (Nat × Nat) → Nat
  | [] => 0
  | (lo, _) :: _ => lo

theorem RevOk_tail {p : Nat × Nat} {r : List (Nat × Nat)} (h : RevOk (p :: r)) : RevOk r := by
  cases r with | nil => trivial | cons _ _ => exact h.2.2.2

theorem RevOk_gap_lt {lo hi : Nat} {r : List (Nat × Nat)} (h : RevOk ((lo, hi) :: r)) :
    ∀ x ∈ r, x.2 + 2 ≤ lo := by
  induction r generalizing lo hi with
  | nil => intro _ hx; cases hx
  | cons q r' ih =>
    rcases q with ⟨qlo, qhi⟩
    have hq := h.2.2
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hq.1
    · have := ih (lo := qlo) (hi := qhi) hq.2 x hx
      have hqq : qlo ≤ qhi := hq.2.1
      omega

theorem rangeListOk_snoc (m : Nat) (xs : List (Nat × Nat)) (lo hi : Nat)
    (hxs : rangeListOk m xs = true) (hgap : ∀ x ∈ xs, x.2 + 2 ≤ lo) (hm : m ≤ lo)
    (hle : lo ≤ hi) (hhi : hi ≤ maxCodePoint) :
    rangeListOk m (xs ++ [(lo, hi)]) = true := by
  induction xs generalizing m with
  | nil => simp [rangeListOk, hm, hle, hhi]
  | cons p r ih =>
    rcases p with ⟨a, b⟩
    simp only [List.cons_append, rangeListOk, Bool.and_eq_true, decide_eq_true_eq] at hxs ⊢
    exact ⟨hxs.1, ih (b + 2) hxs.2 (fun x hx => hgap x (List.mem_cons_of_mem _ hx)) (hgap (a, b) (by simp))⟩

theorem revOk_reverse {acc : List (Nat × Nat)} (h : RevOk acc) :
    rangeListOk 0 acc.reverse = true ∧ ∀ c, MemRanges acc.reverse c ↔ MemRanges acc c := by
  refine ⟨?_, fun c => by simp [MemRanges, List.mem_reverse]⟩
  induction acc with
  | nil => rfl
  | cons p r ih =>
    rcases p with ⟨lo, hi⟩
    rw [List.reverse_cons]
    exact rangeListOk_snoc 0 r.reverse lo hi (ih (RevOk_tail h))
      (fun x hx => RevOk_gap_lt h x (List.mem_reverse.1 hx)) (Nat.zero_le _) h.1 h.2.1

theorem pushRange_ok {acc : List (Nat × Nat)} {lo hi : Nat}
    (hacc : RevOk acc) (hle : lo ≤ hi) (hhi : hi ≤ maxCodePoint) (hord : revHeadLo acc ≤ lo) :
    RevOk (pushRange acc lo hi) ∧ revHeadLo (pushRange acc lo hi) ≤ lo ∧
      (∀ c, MemRanges (pushRange acc lo hi) c ↔ MemRanges acc c ∨ (lo ≤ c ∧ c ≤ hi)) := by
  cases acc with
  | nil => simp [pushRange, RevOk, revHeadLo, hle, hhi, MemRanges]
  | cons p r =>
    rcases p with ⟨plo, phi⟩
    simp only [RevOk] at hacc; simp only [revHeadLo] at hord
    unfold pushRange
    by_cases hmerge : lo ≤ phi + 1
    · simp only [hmerge, ↓reduceIte, revHeadLo, RevOk]
      refine ⟨⟨Nat.le_trans hacc.1 (Nat.le_max_left _ _), Nat.max_le.2 ⟨hacc.2.1, hhi⟩,
        match r, hacc.2.2 with | [], _ => trivial | _ :: _, hr => hr⟩, hord, fun c => ?_⟩
      simp only [memRanges_cons]
      constructor
      · rintro (⟨h1, h2⟩ | hr)
        · by_cases hc : c ≤ phi; exact .inl (.inl ⟨h1, hc⟩); exact .inr ⟨by omega, by omega⟩
        · exact .inl (.inr hr)
      · rintro ((⟨h1, h2⟩ | hr) | ⟨h1, h2⟩)
        · exact .inl ⟨h1, Nat.le_trans h2 (Nat.le_max_left _ _)⟩
        · exact .inr hr
        · exact .inl ⟨Nat.le_trans hord h1, Nat.le_trans h2 (Nat.le_max_right _ _)⟩
    · simp only [hmerge, ↓reduceIte, revHeadLo, RevOk]
      refine ⟨⟨hle, hhi, by omega, hacc⟩, Nat.le_refl _, fun c => ?_⟩
      simp only [memRanges_cons]
      constructor
      · rintro (h | h); exact .inr h; exact .inl h
      · rintro (h | h); exact .inr h; exact .inl h

theorem foldl_pushRange_ok (xs acc : List (Nat × Nat))
    (hxs : ∃ m, rangeListOk m xs = true ∧ revHeadLo acc ≤ m) (hacc : RevOk acc) :
    RevOk (xs.foldl (fun a r => pushRange a r.1 r.2) acc) ∧
      ∀ c, MemRanges (xs.foldl (fun a r => pushRange a r.1 r.2) acc) c ↔ MemRanges acc c ∨ MemRanges xs c := by
  induction xs generalizing acc with
  | nil => simp [hacc]
  | cons p r ih =>
    rcases p with ⟨lo, hi⟩
    obtain ⟨m, hm, hord⟩ := hxs
    have hlo := rangeListOk_head_le hm (lo, hi) (by simp)
    have ⟨hok', hord', hmem'⟩ := pushRange_ok hacc hlo.2.1 hlo.2.2 (Nat.le_trans hord hlo.1)
    have ⟨hokF, hmemF⟩ := ih (pushRange acc lo hi) ⟨hi + 2, rangeListOk_tail hm, Nat.le_trans hord' (by omega)⟩ hok'
    refine ⟨hokF, fun c => ?_⟩
    simp only [List.foldl_cons]
    rw [hmemF c, hmem' c, memRanges_cons]
    constructor
    · rintro ((h | h) | h); exact .inl h; exact .inr (.inl h); exact .inr (.inr h)
    · rintro (h | h | h); exact .inl (.inl h); exact .inl (.inr h); exact .inr h

theorem unionRangesLoop_ok (xs ys acc : List (Nat × Nat))
    (hacc : RevOk acc) (hxs : rangeListOk (revHeadLo acc) xs = true)
    (hys : rangeListOk (revHeadLo acc) ys = true) :
    rangeListOk 0 (unionRangesLoop acc xs ys) = true ∧
      ∀ c, MemRanges (unionRangesLoop acc xs ys) c ↔ MemRanges acc c ∨ MemRanges xs c ∨ MemRanges ys c := by
  cases xs with
  | nil =>
    simp only [unionRangesLoop]
    have ⟨hok, hmem⟩ := foldl_pushRange_ok ys acc ⟨revHeadLo acc, hys, Nat.le_refl _⟩ hacc
    have ⟨hrOk, hrMem⟩ := revOk_reverse hok
    exact ⟨hrOk, fun c => by rw [hrMem c, hmem c]; simp⟩
  | cons x xs' =>
    cases ys with
    | nil =>
      simp only [unionRangesLoop]
      have ⟨hok, hmem⟩ := foldl_pushRange_ok (x :: xs') acc ⟨revHeadLo acc, hxs, Nat.le_refl _⟩ hacc
      have ⟨hrOk, hrMem⟩ := revOk_reverse hok
      exact ⟨hrOk, fun c => by rw [hrMem c, hmem c]; simp⟩
    | cons y ys' =>
      rcases x with ⟨a1, b1⟩; rcases y with ⟨a2, b2⟩
      simp only [unionRangesLoop]
      have ha1 := rangeListOk_head_le hxs (a1, b1) (by simp)
      have ha2 := rangeListOk_head_le hys (a2, b2) (by simp)
      dsimp only at ha1 ha2
      by_cases hcmp : a1 ≤ a2
      · simp only [hcmp, ↓reduceIte]
        have ⟨hok', hord', hmem'⟩ := pushRange_ok hacc ha1.2.1 ha1.2.2 ha1.1
        have ⟨hrOk, hrMem⟩ := unionRangesLoop_ok xs' ((a2, b2) :: ys') (pushRange acc a1 b1) hok'
          (rangeListOk_mono (by omega) (rangeListOk_tail hxs))
          (rangeListOk_mono (by omega) (show rangeListOk a2 ((a2, b2) :: ys') = true by
            simp [rangeListOk, ha2.2.1, ha2.2.2, rangeListOk_tail hys]))
        refine ⟨hrOk, fun c => ?_⟩
        rw [hrMem c, hmem' c]
        simp only [memRanges_cons]
        constructor
        · rintro ((h | h) | h1 | h2); exact .inl h; exact .inr (.inl (.inl h)); exact .inr (.inl (.inr h1)); exact .inr (.inr h2)
        · rintro (h | (h | h1) | h2); exact .inl (.inl h); exact .inl (.inr h); exact .inr (.inl h1); exact .inr (.inr h2)
      · simp only [hcmp, ↓reduceIte]
        have ⟨hok', hord', hmem'⟩ := pushRange_ok hacc ha2.2.1 ha2.2.2 ha2.1
        have ⟨hrOk, hrMem⟩ := unionRangesLoop_ok ((a1, b1) :: xs') ys' (pushRange acc a2 b2) hok'
          (rangeListOk_mono (by omega) (show rangeListOk a1 ((a1, b1) :: xs') = true by
            simp [rangeListOk, ha1.2.1, ha1.2.2, rangeListOk_tail hxs]))
          (rangeListOk_mono (by omega) (rangeListOk_tail hys))
        refine ⟨hrOk, fun c => ?_⟩
        rw [hrMem c, hmem' c]
        simp only [memRanges_cons]
        constructor
        · rintro ((h | h) | h1 | h2); exact .inl h; exact .inr (.inr (.inl h)); exact .inr (.inl h1); exact .inr (.inr (.inr h2))
        · rintro (h | h1 | (h | h2)); exact .inl (.inl h); exact .inr (.inl h1); exact .inl (.inr h); exact .inr (.inr h2)
termination_by xs.length + ys.length

theorem complRangesLoop_ok (cur : Nat) (acc rs : List (Nat × Nat))
    (hacc : RevOk acc) (hgap : ∀ x ∈ acc, x.2 + 2 ≤ cur)
    (hrs : rangeListOk cur rs = true) :
    rangeListOk 0 (complRangesLoop cur acc rs) = true ∧
      ∀ c, MemRanges (complRangesLoop cur acc rs) c ↔
        MemRanges acc c ∨ (cur ≤ c ∧ c ≤ maxCodePoint ∧ ¬ MemRanges rs c) := by
  induction rs generalizing cur acc with
  | nil =>
    simp only [complRangesLoop]
    by_cases hle : cur ≤ maxCodePoint
    · simp only [hle, ↓reduceIte]
      have hok' : RevOk ((cur, maxCodePoint) :: acc) :=
        ⟨hle, Nat.le_refl _, match acc, hgap with | [], _ => trivial | q :: _, hg => ⟨hg q (by simp), hacc⟩⟩
      have ⟨hrOk, hrMem⟩ := revOk_reverse hok'
      refine ⟨hrOk, fun c => ?_⟩
      rw [hrMem c, memRanges_cons, memRanges_nil]
      constructor
      · rintro (h | h); exact .inr ⟨h.1, h.2, fun f => f⟩; exact .inl h
      · rintro (h | ⟨h1, h2, _⟩); exact .inr h; exact .inl ⟨h1, h2⟩
    · simp only [hle, ↓reduceIte]
      have ⟨hrOk, hrMem⟩ := revOk_reverse hacc
      refine ⟨hrOk, fun c => ?_⟩
      rw [hrMem c, memRanges_nil]
      constructor
      · intro h; exact .inl h
      · rintro (h | ⟨h1, h2, _⟩); exact h; omega
  | cons p r ih =>
    rcases p with ⟨lo, hi⟩
    have hp := rangeListOk_head_le hrs (lo, hi) (by simp)
    have ht := rangeListOk_tail hrs
    simp only [complRangesLoop]
    have hacc' : RevOk (if cur < lo then (cur, lo - 1) :: acc else acc) := by
      split
      · refine ⟨by omega, by omega, match acc, hgap with | [], _ => trivial | q :: _, hg => ⟨hg q (by simp), hacc⟩⟩
      · exact hacc
    have hgap' : ∀ x ∈ (if cur < lo then (cur, lo - 1) :: acc else acc), x.2 + 2 ≤ hi + 1 := by
      intro x hx
      split at hx
      · rcases List.mem_cons.1 hx with rfl | hx; omega; exact Nat.le_trans (hgap x hx) (by omega)
      · exact Nat.le_trans (hgap x hx) (by omega)
    have ⟨hrOk, hrMem⟩ := ih (hi + 1) _ hacc' hgap' (rangeListOk_mono (by omega) ht)
    refine ⟨hrOk, fun c => ?_⟩
    rw [hrMem c, memRanges_cons]
    have hrGe : ∀ c', MemRanges r c' → hi + 2 ≤ c' := fun c' ⟨x, hx, hx1, _⟩ =>
      Nat.le_trans (rangeListOk_head_le ht x hx).1 hx1
    have hmem' : MemRanges (if cur < lo then (cur, lo - 1) :: acc else acc) c ↔
        MemRanges acc c ∨ (cur ≤ c ∧ c < lo) := by
      split
      · simp only [memRanges_cons]
        constructor
        · rintro (⟨h1, h2⟩ | h); exact .inr ⟨h1, by omega⟩; exact .inl h
        · rintro (h | ⟨h1, h2⟩); exact .inr h; exact .inl ⟨h1, by omega⟩
      · constructor
        · intro h; exact .inl h
        · rintro (h | ⟨h1, h2⟩); exact h; omega
    rw [hmem']
    constructor
    · rintro ((h | ⟨h1, h2⟩) | ⟨h1, h2, hnr⟩)
      · exact .inl h
      · exact .inr ⟨h1, by omega, fun hc => by rcases hc with hc0 | hrc; omega; have := hrGe c hrc; omega⟩
      · exact .inr ⟨by omega, h2, fun hc => by rcases hc with hc0 | hrc; omega; exact hnr hrc⟩
    · rintro (h | ⟨h1, h2, hn⟩)
      · exact .inl (.inl h)
      · by_cases hlt : c < lo
        · exact .inl (.inr ⟨h1, hlt⟩)
        · exact .inr ⟨Classical.byContradiction fun hle => hn (.inl ⟨by omega, by omega⟩), h2, fun hrc => hn (.inr hrc)⟩

theorem unionRanges_ok (xs ys : Array (Nat × Nat))
    (hx : rangeListOk 0 xs.toList = true) (hy : rangeListOk 0 ys.toList = true) :
    rangeListOk 0 (unionRanges xs ys).toList = true ∧
      ∀ c, MemRanges (unionRanges xs ys).toList c ↔ MemRanges xs.toList c ∨ MemRanges ys.toList c := by
  simpa [unionRanges] using unionRangesLoop_ok xs.toList ys.toList [] trivial hx hy

theorem complRanges_ok (xs : Array (Nat × Nat)) (hx : rangeListOk 0 xs.toList = true) :
    rangeListOk 0 (complRanges xs).toList = true ∧
      ∀ c, MemRanges (complRanges xs).toList c ↔ c ≤ maxCodePoint ∧ ¬ MemRanges xs.toList c := by
  simpa [complRanges] using complRangesLoop_ok 0 [] xs.toList trivial (fun _ h => by cases h) hx

theorem diffRanges_ok (xs ys : Array (Nat × Nat))
    (hx : rangeListOk 0 xs.toList = true) (hy : rangeListOk 0 ys.toList = true) :
    rangeListOk 0 (diffRanges xs ys).toList = true ∧
      ∀ c, MemRanges (diffRanges xs ys).toList c ↔ MemRanges xs.toList c ∧ ¬ MemRanges ys.toList c := by
  have ⟨hc1, hm1⟩ := complRanges_ok xs hx
  have ⟨hu, hmu⟩ := unionRanges_ok (complRanges xs) ys hc1 hy
  have ⟨hc2, hm2⟩ := complRanges_ok (unionRanges (complRanges xs) ys) hu
  refine ⟨hc2, fun c => ?_⟩
  rw [show diffRanges xs ys = complRanges (unionRanges (complRanges xs) ys) from rfl, hm2 c, hmu c, hm1 c]
  constructor
  · rintro ⟨hcMax, hnot⟩
    exact ⟨Classical.byContradiction fun hnx => hnot (.inl ⟨hcMax, hnx⟩), fun hyc => hnot (.inr hyc)⟩
  · rintro ⟨hxc, hnyc⟩
    refine ⟨memRanges_le_max hx hxc, fun h => ?_⟩
    rcases h with ⟨_, hnx⟩ | hyc; exact hnx hxc; exact hnyc hyc

theorem interRanges_ok (xs ys : Array (Nat × Nat))
    (hx : rangeListOk 0 xs.toList = true) (hy : rangeListOk 0 ys.toList = true) :
    rangeListOk 0 (interRanges xs ys).toList = true ∧
      ∀ c, MemRanges (interRanges xs ys).toList c ↔ MemRanges xs.toList c ∧ MemRanges ys.toList c := by
  have ⟨hc1, hm1⟩ := complRanges_ok xs hx
  have ⟨hc2, hm2⟩ := complRanges_ok ys hy
  have ⟨hu, hmu⟩ := unionRanges_ok (complRanges xs) (complRanges ys) hc1 hc2
  have ⟨hc3, hm3⟩ := complRanges_ok _ hu
  refine ⟨hc3, fun c => ?_⟩
  rw [show interRanges xs ys = complRanges (unionRanges (complRanges xs) (complRanges ys)) from rfl, hm3 c, hmu c, hm1 c, hm2 c]
  constructor
  · rintro ⟨hcMax, hnot⟩
    exact ⟨Classical.byContradiction fun hn => hnot (.inl ⟨hcMax, hn⟩),
           Classical.byContradiction fun hn => hnot (.inr ⟨hcMax, hn⟩)⟩
  · rintro ⟨hxc, hyc⟩
    refine ⟨memRanges_le_max hx hxc, fun h => ?_⟩
    rcases h with ⟨_, hnx⟩ | ⟨_, hny⟩; exact hnx hxc; exact hny hyc

theorem coalescePoints_ok (ps : List Nat) (hsort : ps.Pairwise (· < ·)) (hle : ∀ c ∈ ps, c ≤ maxCodePoint) :
    rangeListOk 0 (coalescePoints ps).toList = true ∧
      ∀ c, MemRanges (coalescePoints ps).toList c ↔ c ∈ ps := by
  suffices ∀ (acc : List (Nat × Nat)) (ps' : List Nat),
      ps'.Pairwise (· < ·) → (∀ c ∈ ps', c ≤ maxCodePoint) →
      (∀ c ∈ ps', revHeadLo acc ≤ c) → RevOk acc →
      RevOk (ps'.foldl (fun a c => pushRange a c c) acc) ∧
        ∀ c, MemRanges (ps'.foldl (fun a c => pushRange a c c) acc) c ↔ MemRanges acc c ∨ c ∈ ps' by
    obtain ⟨hok, hmem⟩ := this [] ps hsort hle (fun _ _ => Nat.zero_le _) trivial
    have ⟨hrOk, hrMem⟩ := revOk_reverse hok
    exact ⟨hrOk, fun c => by simpa [coalescePoints] using (hrMem c).trans (by simpa using hmem c)⟩
  intro acc ps' hp hl hord hacc
  induction ps' generalizing acc with
  | nil => simp [hacc]
  | cons p r ih =>
    have hp_head := (List.pairwise_cons.1 hp).1
    have ⟨hok', hord', hmem'⟩ := pushRange_ok hacc (Nat.le_refl p) (hl p (by simp)) (hord p (by simp))
    have ⟨hokF, hmemF⟩ := ih (pushRange acc p p) (List.pairwise_cons.1 hp).2
      (fun c hc => hl c (List.mem_cons_of_mem _ hc))
      (fun c hc => Nat.le_trans hord' (Nat.le_of_lt (hp_head c hc))) hok'
    refine ⟨hokF, fun c => ?_⟩
    simp only [List.foldl_cons]
    rw [hmemF c, hmem' c, List.mem_cons]
    constructor
    · rintro ((h | ⟨h1, h2⟩) | hr); exact .inl h; exact .inr (.inl (by omega)); exact .inr (.inr hr)
    · rintro (h | rfl | hr); exact .inl (.inl h); exact .inl (.inr ⟨Nat.le_refl _, Nat.le_refl _⟩); exact .inr hr

theorem coalesceRanges_ok (rs : List (Nat × Nat)) (hrs : PropSets.rangesOk rs = true) :
    rangeListOk 0 (coalesceRanges rs).toList = true ∧
      ∀ c, MemRanges (coalesceRanges rs).toList c ↔ c ∈ PropSets.expand rs := by
  suffices ∀ (acc : List (Nat × Nat)) (rs' : List (Nat × Nat)),
      PropSets.rangesOk rs' = true →
      (∀ r ∈ rs', revHeadLo acc ≤ r.1) → RevOk acc →
      RevOk (rs'.foldl (fun a r => pushRange a r.1 r.2) acc) ∧
        ∀ c, MemRanges (rs'.foldl (fun a r => pushRange a r.1 r.2) acc) c ↔ MemRanges acc c ∨ MemRanges rs' c by
    obtain ⟨hok, hmem⟩ := this [] rs hrs (fun _ _ => Nat.zero_le _) trivial
    have ⟨hrOk, hrMem⟩ := revOk_reverse hok
    refine ⟨hrOk, fun c => ?_⟩
    rw [show coalesceRanges rs = ((rs.foldl (fun a r => pushRange a r.1 r.2) []).reverse).toArray from rfl]
    simp only [hrMem c, hmem c, memRanges_nil, false_or]
    clear hok hmem hrOk hrMem
    induction rs with
    | nil => simp [PropSets.expand]
    | cons x r ih =>
      rcases x with ⟨a, b⟩
      have ⟨hab1, hab2⟩ := PropSets.rangesOk_head hrs
      have ht := PropSets.rangesOk_tail hrs
      have e : PropSets.expand ((a, b) :: r) = List.range' a (b + 1 - a) ++ PropSets.expand r := rfl
      rw [memRanges_cons, e, List.mem_append, List.mem_range'_1, ih ht]
      have heq : a + (b + 1 - a) = b + 1 := by omega
      rw [heq]
      constructor
      · rintro (⟨h1, h2⟩ | h); exact .inl ⟨by omega, by omega⟩; exact .inr h
      · rintro (⟨h1, h2⟩ | h); exact .inl ⟨by omega, by omega⟩; exact .inr h
  intro acc rs' hrs' hord hacc
  induction rs' generalizing acc with
  | nil => simp [hacc]
  | cons p r ih =>
    rcases p with ⟨a, b⟩
    have hab := PropSets.rangesOk_head hrs'
    have ht := PropSets.rangesOk_tail hrs'
    have ⟨hok', hord', hmem'⟩ := pushRange_ok hacc hab.1 hab.2 (hord (a, b) (by simp))
    have hgap : ∀ q ∈ r, revHeadLo (pushRange acc a b) ≤ q.1 := fun q hq => by
      have hm : q.1 ∈ PropSets.expand r := by
        clear ih hrs' hord hacc hok' hord' hmem'; induction r with
        | nil => cases hq
        | cons z zs ihz =>
          rcases List.mem_cons.1 hq with rfl | hq
          · have hzt := PropSets.rangesOk_head ht
            simp [PropSets.expand, List.mem_range']; omega
          · exact List.mem_append.2 (.inr (ihz (PropSets.rangesOk_tail ht) hq))
      have := PropSets.lt_of_rangesOk hrs' q.1 hm; omega
    have ⟨hokF, hmemF⟩ := ih (pushRange acc a b) ht hgap hok'
    refine ⟨hokF, fun c => ?_⟩
    simp only [List.foldl_cons]
    rw [hmemF c, hmem' c, memRanges_cons]
    constructor
    · rintro ((h | h) | h); exact .inl h; exact .inr (.inl h); exact .inr (.inr h)
    · rintro (h | h | h); exact .inl (.inl h); exact .inl (.inr h); exact .inr h

/-! ## `rangesCount` and `rangesGet` correctness -/

def rangeListCount : List (Nat × Nat) → Nat
  | [] => 0
  | (lo, hi) :: r => (hi + 1 - lo) + rangeListCount r

def rangeListGet : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (lo, hi) :: r, k =>
    let len := hi + 1 - lo
    if k < len then some (lo + k) else rangeListGet r (k - len)

theorem rangesCount_eq (rs : Array (Nat × Nat)) : rangesCount rs = rangeListCount rs.toList := by
  unfold rangesCount; rw [← Array.foldl_toList]
  suffices ∀ l acc, l.foldl (fun (a : Nat) (r : Nat × Nat) => a + (r.2 + 1 - r.1)) acc = acc + rangeListCount l by
    simpa using this rs.toList 0
  intro l; induction l with
  | nil => intro acc; simp [rangeListCount]
  | cons _ r ih => intro acc; simp [rangeListCount, ih, Nat.add_assoc]

theorem rangesGet_eq (rs : Array (Nat × Nat)) (k : Nat) : rangesGet rs k = rangeListGet rs.toList k := by
  unfold rangesGet
  suffices ∀ i k', i ≤ rs.size → rangesGet.go rs i k' = rangeListGet (rs.toList.drop i) k' by
    simpa using this 0 k (Nat.zero_le _)
  intro i k' hi
  induction hlen : rs.size - i generalizing i k' with
  | zero =>
    have heq : i = rs.size := by omega
    subst heq; rw [rangesGet.go]
    have hnot : ¬ rs.size < rs.size := Nat.lt_irrefl _
    rw [List.drop_of_length_le (by simp)]
    simp [hnot, rangeListGet]
  | succ d ih =>
    have hlt : i < rs.size := by omega
    rw [rangesGet.go]; simp only [hlt, ↓reduceDIte]
    rw [List.drop_eq_getElem_cons hlt]; simp only [rangeListGet, Array.getElem_toList]
    split; rfl; exact ih (i + 1) _ (by omega) (by omega)

theorem rangeListGet_spec {m : Nat} {rs : List (Nat × Nat)} (hrs : rangeListOk m rs = true) :
    (∀ k c, rangeListGet rs k = some c → k < rangeListCount rs ∧ c ≤ maxCodePoint ∧ MemRanges rs c) ∧
    (∀ k, k < rangeListCount rs → (rangeListGet rs k).isSome = true) ∧
    (∀ i j c, rangeListGet rs i = some c → rangeListGet rs j = some c → i = j) ∧
    (∀ c, MemRanges rs c → ∃ k, rangeListGet rs k = some c) := by
  induction rs generalizing m with
  | nil => simp [rangeListGet, rangeListCount, MemRanges]
  | cons p r ih =>
    rcases p with ⟨lo, hi⟩
    have hp := rangeListOk_head_le hrs (lo, hi) (by simp)
    have ht := rangeListOk_tail hrs
    obtain ⟨hs, hl, hinj, hex⟩ := ih ht
    have hdisj : ∀ c, c ≤ hi → ¬ MemRanges r c := fun c hc ⟨y, hy, hy1, _⟩ => by
      have := rangeListOk_head_le ht y hy |>.1; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k c hg
      simp only [rangeListGet] at hg
      split at hg
      · cases hg; exact ⟨by simp [rangeListCount]; omega, by omega, (memRanges_cons _ _ _ _).2 (.inl ⟨by omega, by omega⟩)⟩
      · have ⟨hk', hc', hm'⟩ := hs _ _ hg
        exact ⟨by simp [rangeListCount]; omega, hc', (memRanges_cons _ _ _ _).2 (.inr hm')⟩
    · intro k hk
      simp only [rangeListCount] at hk; simp only [rangeListGet]
      split; rfl; exact hl _ (by omega)
    · intro i j c hi' hj'
      simp only [rangeListGet] at hi' hj'
      split at hi' <;> split at hj'
      · have hij := Option.some.inj (hi'.trans hj'.symm); omega
      · cases hi'; exact absurd (hs _ _ hj').2.2 (hdisj _ (by omega))
      · cases hj'; exact absurd (hs _ _ hi').2.2 (hdisj _ (by omega))
      · have := hinj _ _ _ hi' hj'; omega
    · intro c hc
      rcases (memRanges_cons lo hi r c).1 hc with ⟨h1, h2⟩ | hr
      · refine ⟨c - lo, ?_⟩
        simp only [rangeListGet]; split; congr 1; omega; omega
      · obtain ⟨k', hk'⟩ := hex c hr
        exact ⟨(hi + 1 - lo) + k', by simp only [rangeListGet]; split; omega; simp [hk']⟩

/-! ## `WMap (List Nat) Unit` string-set helpers -/

abbrev StrMap := WMap (List Nat) Unit

def stringsWf (m : StrMap) : Prop :=
  ∀ s : List Nat, (m.get s).isSome = true → s.length ≠ 1 ∧ ∀ c ∈ s, c ≤ maxCodePoint

theorem wmap_empty_wf : stringsWf (WMap.empty : StrMap) := by
  intro s hs
  have hs' : ((WMap.empty : StrMap).val.get s).isSome = true := hs
  simp [WMap.empty, OMap.empty, OMap.get] at hs'

theorem wmap_foldl_put (ks : List (List Nat)) (a : StrMap) (s : List Nat) :
    ((ks.foldl (fun m k => m.put k ()) a).get s).isSome = true ↔ (a.get s).isSome = true ∨ s ∈ ks := by
  induction ks generalizing a with
  | nil => simp
  | cons k r ih =>
    simp only [List.foldl_cons, ih]
    rw [show (a.put k ()).get s = if s = k then some () else a.get s from a.property.get_put k () s]
    by_cases hsk : s = k <;> simp [hsk, List.mem_cons]

theorem wmap_foldl_inter (ks : List (List Nat)) (a b : StrMap) (s : List Nat) :
    ((ks.foldl (fun m k => if (b.get k).isSome then m.put k () else m) a).get s).isSome = true ↔
      (a.get s).isSome = true ∨ (s ∈ ks ∧ (b.get s).isSome = true) := by
  induction ks generalizing a with
  | nil => simp
  | cons k r ih =>
    simp only [List.foldl_cons, ih]
    split
    · rename_i hb
      rw [show (a.put k ()).get s = if s = k then some () else a.get s from a.property.get_put k () s]
      by_cases hsk : s = k <;> simp [hsk, List.mem_cons, hb]
    · rename_i hnb
      by_cases hsk : s = k
      · subst hsk; simp [List.mem_cons, hnb]
      · simp [List.mem_cons, hsk]

theorem wmap_foldl_del (ks : List (List Nat)) (a : StrMap) (s : List Nat) :
    ((ks.foldl (fun m k => m.del k) a).get s).isSome = true ↔ (a.get s).isSome = true ∧ s ∉ ks := by
  induction ks generalizing a with
  | nil => simp
  | cons k r ih =>
    simp only [List.foldl_cons, ih]
    rw [show (a.del k).get s = if s = k then none else a.get s from a.property.get_del k s]
    by_cases hsk : s = k <;> simp [hsk, List.mem_cons]

theorem wmap_mem_keys (m : StrMap) (s : List Nat) :
    s ∈ m.keys.toList ↔ (m.get s).isSome = true := by
  rw [show m.get s = m.val.get s from rfl, m.property.mem_keys s]
  constructor
  · intro h; obtain ⟨p, hp, heq⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 h)
    exact ⟨p, by change m.keys[p]? = some s; rw [Array.getElem?_eq_getElem hp, heq]⟩
  · rintro ⟨p, hp⟩
    have hp' : m.keys[p]? = some s := hp
    obtain ⟨hpLt, heq⟩ := Array.getElem?_eq_some_iff.1 hp'
    exact Array.mem_toList_iff.2 (heq ▸ Array.getElem_mem hpLt)

end Engine.Model
