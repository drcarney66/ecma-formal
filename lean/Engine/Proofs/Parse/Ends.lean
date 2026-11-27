module

public import Engine.Parse.Search

@[expose] public section

/-!
# Soundness and completeness of interval end-sets (`Engine.Parse.Ends`)

Every operation on `Ends` (`single`, `isEmpty`, `toList`, `ofIvs`, `ofList`, `ofArray`, `union`,
`diff`, `filter`, `filterM`, `max?`, `maxFrom`) is characterized extensionally in terms of
`Ends.mem` without requiring any sortedness or disjointness invariant on `Ends.ivs`.
-/

namespace Engine.Parse.Ends

/-- Membership of `x` in a raw list of half-open intervals `[lo, hi)`. -/
def inIvs (ivs : List (Nat × Nat)) (x : Nat) : Bool :=
  ivs.any fun (lo, hi) => lo ≤ x && x < hi

theorem mem_eq_inIvs (e : Ends) (x : Nat) : e.mem x = inIvs e.ivs x := rfl

theorem inIvs_nil (x : Nat) : inIvs [] x = false := rfl

theorem inIvs_cons (p : Nat × Nat) (rest : List (Nat × Nat)) (x : Nat) :
    inIvs (p :: rest) x = ((p.1 ≤ x && x < p.2) || inIvs rest x) := rfl

theorem inIvs_append (xs ys : List (Nat × Nat)) (x : Nat) :
    inIvs (xs ++ ys) x = (inIvs xs x || inIvs ys x) := by
  simp [inIvs, List.any_append]

private theorem range_false_of_le {lo hi : Nat} (h : ¬ lo < hi) (x : Nat) :
    (decide (lo ≤ x) && decide (x < hi)) = false := by
  cases h1 : decide (lo ≤ x) <;> cases h2 : decide (x < hi) <;> simp_all
  omega

/-- `consIv` adds `[lo, hi)` to `ivs` extensionally. -/
theorem inIvs_consIv (lo hi : Nat) : ∀ (ivs : List (Nat × Nat)) (x : Nat),
    inIvs (consIv lo hi ivs) x = ((lo ≤ x && x < hi) || inIvs ivs x)
  | [], x => by
    unfold consIv
    split <;> rename_i h
    · simp [inIvs]
    · simp only [inIvs, List.any_nil, Bool.or_false]
      exact (range_false_of_le h x).symm
  | (a, b) :: rest, x => by
    unfold consIv
    split <;> rename_i hba
    · have hab : (decide (a ≤ x) && decide (x < b)) = false := range_false_of_le (by omega) x
      rw [inIvs_consIv lo hi rest x, inIvs_cons]
      dsimp only
      rw [hab, Bool.false_or]
    · split <;> rename_i hhl
      · have hlo : (decide (lo ≤ x) && decide (x < hi)) = false := range_false_of_le (by omega) x
        rw [hlo, Bool.false_or]
      · split <;> rename_i hha
        · rfl
        · split <;> rename_i hbl
          · rw [inIvs_cons, inIvs_consIv lo hi rest x, inIvs_cons]
            cases (decide (lo ≤ x) && decide (x < hi)) <;> cases (decide ((a, b).1 ≤ x) && decide (x < (a, b).2)) <;> simp
          · rw [inIvs_consIv (min lo a) (max hi b) rest x, inIvs_cons, ← Bool.or_assoc]
            congr 1
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            omega

/-- `diffOne` removes `[lo, hi)` from `ivs` extensionally. -/
theorem inIvs_diffOne (lo hi : Nat) : ∀ (ivs : List (Nat × Nat)) (x : Nat),
    inIvs (diffOne lo hi ivs) x = (inIvs ivs x && !(lo ≤ x && x < hi))
  | [], x => rfl
  | (a, b) :: rest, x => by
    unfold diffOne
    split <;> rename_i hba
    · have hab : (decide (a ≤ x) && decide (x < b)) = false := range_false_of_le (by omega) x
      rw [inIvs_diffOne lo hi rest x, inIvs_cons]
      dsimp only
      rw [hab, Bool.false_or]
    · split <;> rename_i hdisj
      · rw [inIvs_cons, inIvs_diffOne lo hi rest x, inIvs_cons]
        dsimp only
        have hboth : (decide (a ≤ x) && decide (x < b) && (decide (lo ≤ x) && decide (x < hi))) = false := by
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hdisj
          cases h1 : decide (a ≤ x) <;> cases h2 : decide (x < b) <;>
            cases h3 : decide (lo ≤ x) <;> cases h4 : decide (x < hi) <;> simp_all
          omega
        revert hboth
        cases (decide (a ≤ x) && decide (x < b)) <;> cases (decide (lo ≤ x) && decide (x < hi)) <;>
          cases (inIvs rest x) <;> simp
      · dsimp only
        rw [inIvs_append, inIvs_append, inIvs_diffOne lo hi rest x, inIvs_cons]
        dsimp only
        have hpart : (inIvs (if a < lo then [(a, lo)] else []) x ||
            inIvs (if hi < b then [(hi, b)] else []) x) =
            ((decide (a ≤ x) && decide (x < b)) && !(decide (lo ≤ x) && decide (x < hi))) := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hdisj
          apply Bool.eq_iff_iff.mpr
          by_cases hal : a < lo <;> by_cases hhb : hi < b <;>
            simp [hal, hhb, inIvs, Bool.or_eq_true, Bool.and_eq_true,
              decide_eq_true_eq, decide_eq_false_iff_not] <;> omega
        rw [hpart]
        cases (decide (a ≤ x) && decide (x < b)) <;> cases (decide (lo ≤ x) && decide (x < hi)) <;>
          cases (inIvs rest x) <;> rfl

theorem mem_empty (x : Nat) : ({} : Ends).mem x = false := rfl

theorem mem_single (j x : Nat) : (single j).mem x = (x == j) := by
  simp only [single, mem, List.any_cons, List.any_nil, Bool.or_false]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

theorem inIvs_foldl_consIv (raw : List (Nat × Nat)) (init : List (Nat × Nat)) (x : Nat) :
    inIvs (raw.foldl (fun acc (lo, hi) => consIv lo hi acc) init) x =
      (inIvs init x || inIvs raw x) := by
  induction raw generalizing init with
  | nil => simp [inIvs]
  | cons p rs ih =>
    simp only [List.foldl_cons, ih, inIvs_consIv, inIvs_cons]
    cases inIvs init x <;> cases (decide (p.1 ≤ x) && decide (x < p.2)) <;> cases inIvs rs x <;> rfl

theorem mem_ofIvs (raw : List (Nat × Nat)) (x : Nat) :
    (ofIvs raw).mem x = inIvs raw x := by
  show inIvs (raw.foldl _ []) x = inIvs raw x
  rw [inIvs_foldl_consIv, inIvs_nil, Bool.false_or]

theorem inIvs_foldl_point (xs : List Nat) (init : List (Nat × Nat)) (x : Nat) :
    inIvs (xs.foldl (fun acc y => consIv y (y + 1) acc) init) x =
      (inIvs init x || xs.contains x) := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, inIvs_consIv, List.contains_cons]
    have hy : (decide (y ≤ x) && decide (x < y + 1)) = (x == y) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
    rw [hy]
    cases inIvs init x <;> cases (x == y) <;> cases ys.contains x <;> rfl

theorem mem_ofList (xs : List Nat) (x : Nat) :
    (ofList xs).mem x = xs.contains x := by
  show inIvs (xs.foldl _ []) x = xs.contains x
  rw [inIvs_foldl_point, inIvs_nil, Bool.false_or]

theorem mem_ofArray (xs : Array Nat) (x : Nat) :
    (ofArray xs).mem x = xs.contains x := by
  rw [ofArray, mem_ofList]
  apply Bool.eq_iff_iff.mpr
  simp

theorem mem_union (a b : Ends) (x : Nat) :
    (a.union b).mem x = (a.mem x || b.mem x) := by
  show inIvs (b.ivs.foldl _ (ofIvs a.ivs).ivs) x = _
  rw [inIvs_foldl_consIv, ← mem_eq_inIvs (ofIvs a.ivs) x, mem_ofIvs, ← mem_eq_inIvs a x, ← mem_eq_inIvs b x]

theorem inIvs_foldl_diffOne (bs : List (Nat × Nat)) (init : List (Nat × Nat)) (x : Nat) :
    inIvs (bs.foldl (fun acc (lo, hi) => diffOne lo hi acc) init) x =
      (inIvs init x && !inIvs bs x) := by
  induction bs generalizing init with
  | nil => simp [inIvs]
  | cons p rs ih =>
    simp only [List.foldl_cons, ih, inIvs_diffOne, inIvs_cons]
    cases inIvs init x <;> cases (decide (p.1 ≤ x) && decide (x < p.2)) <;> cases inIvs rs x <;> rfl

theorem mem_diff (a b : Ends) (x : Nat) :
    (a.diff b).mem x = (a.mem x && !b.mem x) := by
  show inIvs (b.ivs.foldl _ (ofIvs a.ivs).ivs) x = _
  rw [inIvs_foldl_diffOne, ← mem_eq_inIvs (ofIvs a.ivs) x, mem_ofIvs, ← mem_eq_inIvs a x, ← mem_eq_inIvs b x]

theorem isEmpty_iff (e : Ends) : e.isEmpty = true ↔ ∀ x, e.mem x = false := by
  simp only [isEmpty, mem, List.all_eq_true, Bool.eq_false_iff, ne_eq, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, not_exists, not_and]
  constructor
  · intro h x p hp hlo hhi
    have := h p hp
    omega
  · intro h p hp
    exact Classical.byContradiction fun hlt => h p.1 p hp (Nat.le_refl _) (by omega)

theorem mem_toList (e : Ends) (x : Nat) : x ∈ e.toList ↔ e.mem x = true := by
  simp only [toList, mem, List.mem_flatMap, List.mem_range', List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨lo, hi⟩, hp, k, hk, rfl⟩
    exact ⟨(lo, hi), hp, by omega, by omega⟩
  · rintro ⟨⟨lo, hi⟩, hp, hlo, hhi⟩
    exact ⟨(lo, hi), hp, x - lo, by omega, by omega⟩

theorem mem_toArray (e : Ends) (x : Nat) : x ∈ e.toArray ↔ e.mem x = true := by
  rw [toArray, List.mem_toArray, mem_toList]

theorem mem_filter (e : Ends) (p : Nat → Bool) (x : Nat) :
    (e.filter p).mem x = (e.mem x && p x) := by
  rw [filter, mem_ofList]
  apply Bool.eq_iff_iff.mpr
  simp [List.mem_filter, mem_toList]

private theorem sm_bind_ok {T α β : Type} {m : SM T α} {f : α → SM T β} {st : St T} {b : β} {st' : St T}
    (h : (m >>= f).run st = .ok (b, st')) :
    ∃ a st1, m.run st = .ok (a, st1) ∧ (f a).run st1 = .ok (b, st') := by
  rw [StateT.run_bind] at h
  cases hm : m.run st with
  | error e => rw [hm] at h; cases h
  | ok p => rw [hm] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem filterListM_sm_spec {T : Type} {Inv : St T → Prop} {P : Nat → Prop}
    {p : Nat → SM T Bool}
    (hp : ∀ x st, Inv st → ∀ b st', (p x).run st = .ok (b, st') →
      Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
      st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧ (b = true ↔ P x)) :
    ∀ (xs : List Nat) (st : St T) (kept : List Nat) (st' : St T),
      Inv st →
      (filterListM p xs).run st = .ok (kept, st') →
      Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
      st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
      ∀ y, y ∈ kept ↔ (y ∈ xs ∧ P y)
  | [], st, kept, st', hinv, hrun => by
    unfold filterListM at hrun
    cases hrun
    exact ⟨hinv, rfl, rfl, rfl, rfl, rfl, rfl, fun y => by simp⟩
  | x :: xs, st, kept, st', hinv, hrun => by
    unfold filterListM at hrun
    obtain ⟨b, st1, hpx, hrun⟩ := sm_bind_ok hrun
    obtain ⟨rest, st2, hrest, hrun⟩ := sm_bind_ok hrun
    have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hb⟩ := hp x st hinv b st1 hpx
    have ⟨hi2, hm2, ha2, hrd2, hfw2, hfi2, hfar2, hmem⟩ := filterListM_sm_spec hp xs st1 rest st2 hi1 hrest
    cases hrun
    refine ⟨hi2, hm2.trans hm1, ha2.trans ha1, hrd2.trans hrd1, hfw2.trans hfw1,
      hfi2.trans hfi1, hfar2.trans hfar1, fun y => ?_⟩
    cases b with
    | true =>
      simp only [↓reduceIte, List.mem_cons, hmem]
      have hpx' : P x := hb.mp rfl
      constructor
      · rintro (rfl | ⟨hy, hpy⟩)
        · exact ⟨Or.inl rfl, hpx'⟩
        · exact ⟨Or.inr hy, hpy⟩
      · rintro ⟨rfl | hy, hpy⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hy, hpy⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, hmem]
      constructor
      · rintro ⟨hy, hpy⟩; exact ⟨Or.inr hy, hpy⟩
      · rintro ⟨rfl | hy, hpy⟩
        · exact absurd (hb.mpr hpy) Bool.false_ne_true
        · exact ⟨hy, hpy⟩

theorem filterM_sm_spec {T : Type} {Inv : St T → Prop} {P : Nat → Prop}
    {p : Nat → SM T Bool}
    (hp : ∀ x st, Inv st → ∀ b st', (p x).run st = .ok (b, st') →
      Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
      st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧ (b = true ↔ P x))
    (e : Ends) (st : St T) (out : Ends) (st' : St T)
    (hinv : Inv st)
    (hrun : (e.filterM p).run st = .ok (out, st')) :
    Inv st' ∧ st'.memo = st.memo ∧ st'.active = st.active ∧ st'.reads = st.reads ∧
    st'.fwd = st.fwd ∧ st'.first = st.first ∧ st'.far = st.far ∧
    ∀ y, out.mem y = true ↔ (e.mem y = true ∧ P y) := by
  unfold filterM at hrun
  obtain ⟨kept, st1, hf, hrun⟩ := sm_bind_ok hrun
  have ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, hkept⟩ := filterListM_sm_spec hp e.toList st kept st1 hinv hf
  cases hrun
  refine ⟨hi1, hm1, ha1, hrd1, hfw1, hfi1, hfar1, fun y => ?_⟩
  rw [mem_ofList, List.contains_iff_mem, hkept, mem_toList]

/-- Specification of the interval fold computing `Ends.max?`. -/
theorem foldl_max_spec : ∀ (ivs : List (Nat × Nat)) (acc : Option Nat),
    match ivs.foldl (fun acc (lo, hi) =>
      if lo < hi then some (match acc with | some m => max m (hi - 1) | none => hi - 1) else acc) acc with
    | none => acc = none ∧ ∀ x, inIvs ivs x = false
    | some m =>
      ((acc = some m ∨ inIvs ivs m = true) ∧
       (∀ m0, acc = some m0 → m0 ≤ m) ∧
       (∀ x, inIvs ivs x = true → x ≤ m))
  | [], none => ⟨rfl, fun _ => rfl⟩
  | [], some m => ⟨Or.inl rfl, fun _ h => by cases h; exact Nat.le_refl _, fun _ h => nomatch h⟩
  | (lo, hi) :: rest, acc => by
    simp only [List.foldl_cons]
    generalize hf : rest.foldl _ _ = res
    by_cases hlt : lo < hi
    · simp only [hlt, ↓reduceIte] at hf
      let next := match acc with | some m0 => max m0 (hi - 1) | none => hi - 1
      have ih := foldl_max_spec rest (some next)
      rw [hf] at ih
      cases res with
      | none => exact nomatch ih.1
      | some m =>
        obtain ⟨hmem, hge, hub⟩ := ih
        have hnext : next ≤ m := hge next rfl
        refine ⟨?_, ?_, ?_⟩
        · rcases hmem with hnm | hrm
          · cases hnm
            cases acc with
            | none =>
              right; rw [inIvs_cons, Bool.or_eq_true]; left
              simp only [Bool.and_eq_true, decide_eq_true_eq, next]; omega
            | some m0 =>
              by_cases hm : m0 ≤ hi - 1
              · right; rw [inIvs_cons, Bool.or_eq_true]; left
                have : max m0 (hi - 1) = hi - 1 := Nat.max_eq_right hm
                simp only [next, this, Bool.and_eq_true, decide_eq_true_eq]; omega
              · left; simp only [next]; congr 1; omega
          · right; rw [inIvs_cons, hrm, Bool.or_true]
        · intro m0 hm0
          subst hm0
          simp only [next] at hnext
          omega
        · intro x hx
          rw [inIvs_cons, Bool.or_eq_true] at hx
          rcases hx with hx | hx
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
            cases acc <;> simp only [next] at hnext <;> omega
          · exact hub x hx
    · simp only [hlt, ↓reduceIte] at hf
      have ih := foldl_max_spec rest acc
      rw [hf] at ih
      have hfalse : ∀ x, (decide (lo ≤ x) && decide (x < hi)) = false := fun x => range_false_of_le hlt x
      cases res with
      | none =>
        refine ⟨ih.1, fun x => ?_⟩
        rw [inIvs_cons]; dsimp only; rw [hfalse, Bool.false_or]; exact ih.2 x
      | some m =>
        obtain ⟨hmem, hge, hub⟩ := ih
        refine ⟨?_, hge, ?_⟩
        · rcases hmem with ha | hr
          · exact Or.inl ha
          · right; rw [inIvs_cons, hr, Bool.or_true]
        · intro x hx
          rw [inIvs_cons] at hx; dsimp only at hx; rw [hfalse, Bool.false_or] at hx
          exact hub x hx

theorem max?_none {e : Ends} (h : e.max? = none) (x : Nat) : e.mem x = false := by
  have hs := foldl_max_spec e.ivs none
  revert hs
  change (match e.max? with | none => _ | some _ => _) → _
  rw [h]
  intro hs
  exact hs.2 x

theorem max?_some {e : Ends} {m : Nat} (h : e.max? = some m) :
    e.mem m = true ∧ ∀ x, e.mem x = true → x ≤ m := by
  have hs := foldl_max_spec e.ivs none
  revert hs
  change (match e.max? with | none => _ | some _ => _) → _
  rw [h]
  intro hs
  obtain ⟨hmem, -, hub⟩ := hs
  rcases hmem with hn | hm
  · cases hn
  · exact ⟨hm, hub⟩

theorem maxFrom_ge (e : Ends) (k : Nat) : k ≤ e.maxFrom k := by
  unfold maxFrom
  cases e.max? with
  | none => exact Nat.le_refl _
  | some j => exact Nat.le_max_left k j

theorem maxFrom_ub (e : Ends) (k x : Nat) (hx : e.mem x = true) : x ≤ e.maxFrom k := by
  unfold maxFrom
  cases hm : e.max? with
  | none => rw [max?_none hm x] at hx; cases hx
  | some m =>
    have := (max?_some hm).2 x hx
    exact Nat.le_trans this (Nat.le_max_right k m)

theorem maxFrom_eq_or_mem (e : Ends) (k : Nat) :
    e.maxFrom k = k ∨ (k < e.maxFrom k ∧ e.mem (e.maxFrom k) = true) := by
  unfold maxFrom
  cases hm : e.max? with
  | none => exact Or.inl rfl
  | some m =>
    dsimp only
    by_cases hkm : m ≤ k
    · left; exact Nat.max_eq_left hkm
    · right
      have hmax : max k m = m := Nat.max_eq_right (by omega)
      rw [hmax]
      exact ⟨by omega, (max?_some hm).1⟩

end Engine.Parse.Ends
