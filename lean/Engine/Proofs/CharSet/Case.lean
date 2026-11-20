module

public import Engine.Proofs.CharSet.Base

@[expose] public section

/-!
# Case-folding laws of `Engine.Impl` (`csNoScf`, `csCanonExtra`, `csHasCanon`)
-/

namespace Engine.Impl

open Ecma Engine.Model

private theorem toUpper_single (c : Nat) :
    Impl.toUpper (Impl.seqPush Impl.seqNil (.int c)) =
      (Engine.upperPoints [c]).toArray.map fun (d : Nat) => MathVal.int d := by
  have h : List.filterMap MathVal.idx (Impl.seqPush Impl.seqNil (.int c)).toList = [c] := by
    change List.filterMap MathVal.idx [MathVal.int c] = [c]
    simp [MathVal.idx]
  change ((Engine.upperPoints (List.filterMap MathVal.idx (Impl.seqPush Impl.seqNil (.int c)).toList)).toArray.map fun (d : Nat) => MathVal.int d) = _
  rw [h]

private def canonUpperBody (M : Model) (c : M.Math) (mapped : M.Seq M.Math) : M.Math :=
  if M.eq (M.seqLen mapped) (M.ofNat 1) then
    match M.seqGet mapped (M.ofNat 0) with
    | some d => if M.lt (M.ofNat 0xFFFF) d || (!M.lt c (M.ofNat 128) && M.lt d (M.ofNat 128)) then c else d
    | none => c
  else c

private theorem canonChar_true_false (M : Model) (c : M.Math) :
    Model.canonChar M true false c = canonUpperBody M c (M.toUpper (M.seqPush M.seqNil c)) := rfl

private theorem canonChar_false_eval (c : Nat) (up : Array MathVal) :
    canonUpperBody Impl (.int c) up =
    match up.toList with
    | [d] => if Impl.lt (Impl.ofNat 0xFFFF) d || (!Impl.lt (MathVal.int c) (Impl.ofNat 128) && Impl.lt d (Impl.ofNat 128)) then .int c else d
    | _ => .int c := by
  unfold canonUpperBody
  cases h : up.toList with
  | nil =>
    have hs : up.size = 0 := by rw [← Array.length_toList, h]; rfl
    change (if decide ((up.size : Int) = 1) = true then _ else MathVal.int c) = _
    rw [hs]; rfl
  | cons d r =>
    cases r with
    | nil =>
      have hu : up = #[d] := Array.ext' (by rw [h])
      subst hu; rfl
    | cons e r' =>
      have hs : ¬ up.size = 1 := by rw [← Array.length_toList, h]; simp
      have hfalse : decide ((up.size : Int) = 1) = false := decide_eq_false (by omega)
      change (if decide ((up.size : Int) = 1) = true then _ else MathVal.int c) = _
      rw [hfalse]; rfl

private theorem map_toList_int (l : List Nat) :
    (l.toArray.map fun (d : Nat) => MathVal.int d).toList = l.map fun (d : Nat) => MathVal.int d := by
  simp

private theorem impl_lt_ofNat (a b : Nat) : Impl.lt (Impl.ofNat a) (.int b) = decide (a < b) := by
  change decide ((a : Int) < (b : Int)) = decide (a < b)
  by_cases h : a < b
  · rw [decide_eq_true (by omega), decide_eq_true h]
  · rw [decide_eq_false (by omega), decide_eq_false h]

private theorem impl_lt_toOfNat (a b : Nat) : Impl.lt (MathVal.int a) (Impl.ofNat b) = decide (a < b) := by
  change decide ((a : Int) < (b : Int)) = decide (a < b)
  by_cases h : a < b
  · rw [decide_eq_true (by omega), decide_eq_true h]
  · rw [decide_eq_false (by omega), decide_eq_false h]

private theorem canonUpperBody_map_eval (c : Nat) (us : List Nat) :
    canonUpperBody Impl (.int c) (us.toArray.map fun (d : Nat) => MathVal.int d) =
    match us with
    | [d] => if d ≤ 0xFFFF && !(128 ≤ c && d < 128) then .int d else .int c
    | _ => .int c := by
  rw [canonChar_false_eval, map_toList_int]
  cases us with
  | nil => rfl
  | cons d r =>
    cases r with
    | nil =>
      simp only [List.map_cons, List.map_nil]
      have hcond : (Impl.lt (Impl.ofNat 0xFFFF) (.int d) || (!Impl.lt (MathVal.int c) (Impl.ofNat 128) && Impl.lt (.int d) (Impl.ofNat 128))) =
          !(decide (d ≤ 0xFFFF) && !(decide (128 ≤ c) && decide (d < 128))) := by
        rw [impl_lt_ofNat, impl_lt_toOfNat, impl_lt_toOfNat]
        have h1 : decide (0xFFFF < d) = !decide (d ≤ 0xFFFF) := by
          by_cases h : d ≤ 0xFFFF
          · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
          · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl
        have h2 : decide (c < 128) = !decide (128 ≤ c) := by
          by_cases h : 128 ≤ c
          · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
          · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl
        rw [h1, h2]
        cases decide (d ≤ 0xFFFF) <;> cases decide (128 ≤ c) <;> cases decide (d < 128) <;> rfl
      rw [hcond]
      cases (decide (d ≤ 0xFFFF) && !(decide (128 ≤ c) && decide (d < 128))) <;> simp
    | cons _ _ => rfl

private theorem canonChar_upper_isPoint_gen (cn : Nat) (hcn : cn ≤ maxCodePoint) (up : Array MathVal)
    (hup : ∀ i d, Impl.seqGet up i = some d → Model.isPoint Impl d) :
    Model.isPoint Impl (canonUpperBody Impl (.int cn) up) := by
  rw [canonChar_false_eval]
  cases hl : up.toList with
  | nil => dsimp only; exact nat_isPoint cn hcn
  | cons d r =>
    cases r with
    | nil =>
      dsimp only
      have hk : up[0]? = some d := by rw [← Array.getElem?_toList, hl]; rfl
      have hd0 : Impl.seqGet up (Impl.ofNat 0) = some d := by
        change (MathVal.idx (.int 0)).bind (fun k => up[k]?) = some d
        simpa [MathVal.idx] using hk
      have hdPt := hup (Impl.ofNat 0) d hd0
      split
      · exact nat_isPoint cn hcn
      · exact hdPt
    | cons _ _ => dsimp only; exact nat_isPoint cn hcn

def caseRunsOk (checkDelta : Bool) (runs : List _root_.Unicode.CaseRun) : Bool :=
  let rec asc : Option Nat → List _root_.Unicode.CaseRun → Bool
    | _, [] => true
    | prev, r :: rs =>
      (match prev with | none => true | some l => l < r.first) &&
      0 < r.stride && r.first ≤ r.last && r.last ≤ maxCodePoint &&
      decide (0 ≤ (r.first : Int) + r.delta) && decide ((r.last : Int) + r.delta ≤ maxCodePoint) &&
      (!checkDelta || decide (r.delta ≠ 0)) && asc (some r.last) rs
  asc none runs

def upperSpecOk : Option Nat → List (Nat × List Nat) → Bool
  | _, [] => true
  | prev, (k, m) :: r => (match prev with | none => true | some p => p < k) &&
      2 ≤ (m.filter (· ≤ maxCodePoint)).length && upperSpecOk (some k) r

theorem scfRuns_ok : caseRunsOk true _root_.Unicode.simpleCaseFoldingRuns = true := by decide +kernel
theorem upperRuns_ok : caseRunsOk false _root_.Unicode.uppercaseRuns = true := by decide +kernel
theorem upperSpec_ok : upperSpecOk none _root_.Unicode.uppercaseSpecial = true := by decide +kernel

theorem caseRunsOk_spec {chk : Bool} {runs : List _root_.Unicode.CaseRun} (h : caseRunsOk chk runs = true) :
    (∀ r ∈ runs, 0 < r.stride ∧ r.first ≤ r.last ∧ r.last ≤ maxCodePoint ∧
      0 ≤ (r.first : Int) + r.delta ∧ (r.last : Int) + r.delta ≤ maxCodePoint ∧ (chk = true → r.delta ≠ 0)) ∧
    runs.Pairwise (fun a b => a.last < b.first) := by
  unfold caseRunsOk at h
  suffices ∀ prev rs, caseRunsOk.asc chk prev rs = true →
      (∀ r ∈ rs, (∀ l, prev = some l → l < r.first) ∧ 0 < r.stride ∧ r.first ≤ r.last ∧ r.last ≤ maxCodePoint ∧
        0 ≤ (r.first : Int) + r.delta ∧ (r.last : Int) + r.delta ≤ maxCodePoint ∧ (chk = true → r.delta ≠ 0)) ∧
      rs.Pairwise (fun a b => a.last < b.first) by
    have ⟨h1, h2⟩ := this none runs h; exact ⟨fun r hr => (h1 r hr).2, h2⟩
  intro prev rs; induction rs generalizing prev with
  | nil => intro _; simp
  | cons r rs' ih =>
    intro hr
    simp only [caseRunsOk.asc, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hr
    obtain ⟨⟨⟨⟨⟨⟨hp, hs⟩, hfl⟩, hlm⟩, hd0⟩, hdm⟩, hdne⟩ := hr.1
    have ⟨ih1, ih2⟩ := ih (some r.last) hr.2
    refine ⟨fun x hx => (List.mem_cons.1 hx).elim
      (fun heq => by subst heq; exact ⟨fun l hl => by subst hl; exact of_decide_eq_true hp, hs, hfl, hlm, hd0, hdm, fun hc => by subst hc; simp_all⟩)
      (fun hm => ⟨fun l hl => by subst hl; have := of_decide_eq_true hp; have := (ih1 x hm).1 r.last rfl; omega, (ih1 x hm).2⟩),
      List.pairwise_cons.2 ⟨fun y hy => (ih1 y hy).1 r.last rfl, ih2⟩⟩

theorem lookupRunsA_iff {chk : Bool} {runs : List _root_.Unicode.CaseRun} (hok : caseRunsOk chk runs = true) (c d : Nat) :
    _root_.Unicode.lookupRunsA ⟨runs⟩ c = some d ↔
      ∃ r ∈ runs, r.first ≤ c ∧ c ≤ r.last ∧ (c - r.first) % r.stride = 0 ∧ d = ((c : Int) + r.delta).toNat := by
  have ⟨hbounds, hpw⟩ := caseRunsOk_spec hok
  have hsort : ∀ i j (hi : i < (⟨runs⟩ : Array _root_.Unicode.CaseRun).size)
      (hj : j < (⟨runs⟩ : Array _root_.Unicode.CaseRun).size), i ≤ j → runs[i].first ≤ runs[j].first := fun i j hi hj hij =>
    (Nat.lt_or_eq_of_le hij).elim
      (fun hlt => by have := List.pairwise_iff_getElem.1 hpw i j (by simpa using hi) (by simpa using hj) hlt; have := hbounds runs[i] (List.getElem_mem _); omega)
      (fun h => h ▸ Nat.le_refl _)
  obtain ⟨hnone, hsome⟩ := lastLE_spec _root_.Unicode.CaseRun.first ⟨runs⟩ c hsort
  unfold _root_.Unicode.lookupRunsA
  constructor
  · intro h
    cases hl : _root_.Unicode.lastLE _root_.Unicode.CaseRun.first ⟨runs⟩ c with
    | none => simp [hl] at h
    | some r =>
      rw [hl] at h; dsimp only at h
      obtain ⟨idx, hidx, heq, hfc, _⟩ := hsome r hl
      by_cases hcond : c ≤ r.last ∧ (c - r.first) % r.stride = 0
      · have h' : ((c : Int) + r.delta).toNat = d := by simpa [hcond] using h
        subst h'
        rw [Array.getElem?_eq_getElem hidx] at heq; cases heq
        exact ⟨runs[idx], List.getElem_mem (by simpa using hidx), hfc, hcond.1, hcond.2, rfl⟩
      · simp only [hcond, ↓reduceIte] at h; cases h
  · rintro ⟨r, hm, hfc, hcl, hmod, rfl⟩
    obtain ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.1 hm
    cases hl : _root_.Unicode.lastLE _root_.Unicode.CaseRun.first ⟨runs⟩ c with
    | none => have := hnone hl j (by simpa using hj); change c < runs[j].first at this; rw [hjEq] at this; omega
    | some r' =>
      obtain ⟨idx, hidx, heq, hfr', hmax⟩ := hsome r' hl
      have hjIdx := hmax j (by simpa using hj) (by change runs[j].first ≤ c; rw [hjEq]; exact hfc)
      have hidxEq : runs[idx] = r' := by have : (⟨runs⟩ : Array _)[idx]? = some runs[idx] := Array.getElem?_eq_getElem hidx; rw [this] at heq; cases heq; rfl
      rcases Nat.lt_or_eq_of_le hjIdx with hlt | rfl
      · have := List.pairwise_iff_getElem.1 hpw j idx hj (by simpa using hidx) hlt; rw [hjEq, hidxEq] at this; omega
      · have hrr' : r' = r := by rw [← hidxEq, hjEq]
        subst hrr'; simp [hcl, hmod]

theorem runPointsFuel_mem (fuel c last stride : Nat) (hstride : 0 < stride) (hc : c ≤ last)
    (hf : (last - c) / stride + 1 ≤ fuel) (acc : List Nat) (x : Nat) :
    x ∈ runPointsFuel fuel c last stride acc ↔ x ∈ acc ∨ (c ≤ x ∧ x ≤ last ∧ (x - c) % stride = 0) := by
  suffices ∀ f c' ac, x ∈ runPointsFuel f c' last stride ac ↔ x ∈ ac ∨ ∃ k < f, x = c' + k * stride ∧ x ≤ last by
    rw [this fuel c acc]
    constructor
    · rintro (h | ⟨k, _, rfl, hxl⟩); exact .inl h; exact .inr ⟨by omega, hxl, by simp⟩
    · rintro (h | ⟨h1, h2, hmod⟩); exact .inl h
      refine .inr ⟨(x - c) / stride, Nat.lt_of_le_of_lt (Nat.div_le_div_right (by omega)) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hf), ?_, h2⟩
      have : (x - c) / stride * stride = x - c := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod); omega
  intro f; induction f with
  | zero => intro c' ac; simp [runPointsFuel]
  | succ k ih =>
    intro c' ac; unfold runPointsFuel; by_cases hle : c' ≤ last
    · simp only [hle, ↓reduceIte, ih (c' + stride) (c' :: ac), List.mem_cons]
      constructor
      · rintro ((rfl | ha) | ⟨j, hj, rfl, hx⟩); exact .inr ⟨0, by omega, by simp, hle⟩; exact .inl ha; exact .inr ⟨j + 1, by omega, by rw [Nat.succ_mul]; omega, hx⟩
      · rintro (ha | ⟨j, hj, rfl, hx⟩); exact .inl (.inr ha)
        cases j with | zero => exact .inl (.inl (by simp)) | succ j' => exact .inr ⟨j', by omega, by rw [Nat.succ_mul]; omega, hx⟩
    · simp only [hle, ↓reduceIte, List.mem_reverse]
      constructor
      · intro h; exact .inl h
      · rintro (h | ⟨_, _, rfl, hx⟩); exact h; omega

theorem scfPoint?_iff_pairs {c : Nat} (hc : c ≤ maxCodePoint) (d : Nat) :
    Engine.scfPoint? c = some d ↔ (c, d) ∈ scfPairsList := by
  have ⟨hbounds, _⟩ := caseRunsOk_spec scfRuns_ok
  unfold Engine.scfPoint?; have hcMax : c ≤ maxPoint := hc
  simp only [hcMax, ↓reduceIte, Option.filter_eq_some_iff]
  rw [show _root_.Unicode.simpleCaseFoldingRunsA = ⟨_root_.Unicode.simpleCaseFoldingRuns⟩ from rfl,
    lookupRunsA_iff scfRuns_ok c d]
  constructor
  · rintro ⟨⟨r, hm, hfc, hcl, hmod, rfl⟩, _⟩
    have hr := hbounds r hm
    refine List.mem_flatMap.2 ⟨r, hm, List.mem_map.2 ⟨c, ?_, rfl⟩⟩
    simp only [hr.1, hr.2.1, and_self, ↓reduceIte]
    exact (runPointsFuel_mem _ _ _ _ hr.1 hr.2.1 (Nat.le_refl _) [] c).2 (.inr ⟨hfc, hcl, hmod⟩)
  · intro hm; unfold scfPairsList at hm
    obtain ⟨r, hrm, hx⟩ := List.mem_flatMap.1 hm
    obtain ⟨c', hc', heq⟩ := List.mem_map.1 hx; cases heq
    have hr := hbounds r hrm; simp only [hr.1, hr.2.1, and_self, ↓reduceIte] at hc'
    rcases (runPointsFuel_mem _ _ _ _ hr.1 hr.2.1 (Nat.le_refl _) [] c).1 hc' with h | ⟨h1, h2, h3⟩
    · cases h
    · exact ⟨⟨r, hrm, h1, h2, h3, rfl⟩, decide_eq_true (by unfold maxPoint; unfold maxCodePoint at *; omega)⟩

theorem canonChar_pair_iff (u : Bool) {c : Nat} (hc : c ≤ maxCodePoint) (d : Nat) :
    let pairs := if u then scfPairsList else nonUCanonPairsList
    (Model.canonChar Impl true u (.int c) = .int d ↔
      (d ≠ c ∧ (c, d) ∈ pairs) ∨ (d = c ∧ ¬ ∃ d', (c, d') ∈ pairs)) ∧
    (∀ p ∈ pairs, p.1 ≤ maxCodePoint ∧ p.2 ≤ maxCodePoint ∧ p.2 ≠ p.1) := by
  have ⟨hbS, _⟩ := caseRunsOk_spec scfRuns_ok
  have ⟨hbU, _⟩ := caseRunsOk_spec upperRuns_ok
  have hsp : ∀ prev sp, upperSpecOk prev sp = true →
      sp.Pairwise (fun a b => a.1 < b.1) ∧ (∀ x ∈ sp, 2 ≤ (x.2.filter (· ≤ maxCodePoint)).length) ∧
        ∀ p, prev = some p → ∀ x ∈ sp, p < x.1 := by
    intro prev sp; induction sp generalizing prev with
    | nil => intro _; simp
    | cons x r ih =>
      rcases x with ⟨k, m⟩; intro h
      cases prev with
      | none =>
        simp only [upperSpecOk, Bool.and_eq_true, decide_eq_true_eq] at h
        have ⟨ih1, ih2, ih3⟩ := ih (some k) h.2
        exact ⟨List.pairwise_cons.2 ⟨fun y hy => ih3 k rfl y hy, ih1⟩,
          fun y hy => (List.mem_cons.1 hy).elim (· ▸ h.1.2) (ih2 y),
          fun _ hp _ _ => by cases hp⟩
      | some p =>
        simp only [upperSpecOk, Bool.and_eq_true, decide_eq_true_eq] at h
        have ⟨ih1, ih2, ih3⟩ := ih (some k) h.2
        exact ⟨List.pairwise_cons.2 ⟨fun y hy => ih3 k rfl y hy, ih1⟩,
          fun y hy => (List.mem_cons.1 hy).elim (· ▸ h.1.2) (ih2 y),
          fun q hq y hy => by cases hq; exact (List.mem_cons.1 hy).elim (· ▸ h.1.1) fun hm => Nat.lt_trans h.1.1 (ih3 k rfl y hm)⟩
  have hspOk := hsp none _ upperSpec_ok
  have hspSort : ∀ i j (hi : i < _root_.Unicode.uppercaseSpecialA.size)
      (hj : j < _root_.Unicode.uppercaseSpecialA.size),
      i < j → _root_.Unicode.uppercaseSpecialA[i].1 < _root_.Unicode.uppercaseSpecialA[j].1 :=
    fun i j hi hj hij => List.pairwise_iff_getElem.1 hspOk.1 i j
      (by simpa [_root_.Unicode.uppercaseSpecialA] using hi)
      (by simpa [_root_.Unicode.uppercaseSpecialA] using hj) hij
  have hnonU : ∀ c' d', c' ≤ maxCodePoint →
      ((Engine.upperPoints [c'] = [d'] ∧ d' ≤ 0xFFFF ∧ !(128 ≤ c' && d' < 128) ∧ d' ≠ c') ↔ (c', d') ∈ nonUCanonPairsList) := by
    intro c' d' hc'
    have hmem_run : (c', d') ∈ nonUCanonPairsList ↔
        _root_.Unicode.lookupSortedA _root_.Unicode.uppercaseSpecialA c' = none ∧
        d' ≤ 0xFFFF ∧ !(128 ≤ c' && d' < 128) ∧ d' ≠ c' ∧
        _root_.Unicode.lookupRunsA _root_.Unicode.uppercaseRunsA c' = some d' := by
      rw [show _root_.Unicode.uppercaseRunsA = ⟨_root_.Unicode.uppercaseRuns⟩ from rfl,
        lookupRunsA_iff upperRuns_ok c' d']; unfold nonUCanonPairsList
      simp only [List.mem_flatMap, List.mem_filterMap]
      constructor
      · rintro ⟨r, hrm, u', hu', hfm⟩; have hr := hbU r hrm
        simp only [hr.1, hr.2.1, and_self, ↓reduceIte] at hu'
        rcases (runPointsFuel_mem _ _ _ _ hr.1 hr.2.1 (Nat.le_refl _) [] u').1 hu' with h | ⟨h1, h2, h3⟩
        · cases h
        · cases hsl : _root_.Unicode.lookupSortedA _root_.Unicode.uppercaseSpecialA u' with
          | some _ => simp [hsl] at hfm
          | none =>
            rw [hsl] at hfm; dsimp only at hfm
            by_cases hcnd : (decide (((u' : Int) + r.delta).toNat ≤ 0xFFFF) && !(decide (128 ≤ u') && decide (((u' : Int) + r.delta).toNat < 128)) && (((u' : Int) + r.delta).toNat != u')) = true
            · simp only [hcnd, ↓reduceIte, Option.some.injEq] at hfm
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hfm
              simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hcnd
              exact ⟨hsl, hcnd.1.1, hcnd.1.2, hcnd.2, ⟨r, hrm, h1, h2, h3, rfl⟩⟩
            · simp only [hcnd, Bool.false_eq_true, ↓reduceIte] at hfm; cases hfm
      · rintro ⟨hsN, hd1, hd2, hd3, r, hrm, h1, h2, h3, rfl⟩; have hr := hbU r hrm
        refine ⟨r, hrm, c', ?_, ?_⟩
        · simp only [hr.1, hr.2.1, and_self, ↓reduceIte]; exact (runPointsFuel_mem _ _ _ _ hr.1 hr.2.1 (Nat.le_refl _) [] c').2 (.inr ⟨h1, h2, h3⟩)
        · rw [hsN]; dsimp only
          have hb : (decide (((c' : Int) + r.delta).toNat ≤ 0xFFFF) && !(decide (128 ≤ c') && decide (((c' : Int) + r.delta).toNat < 128)) && (((c' : Int) + r.delta).toNat != c')) = true := by
            rw [decide_eq_true hd1]; simp only [Bool.true_and, hd2, bne_iff_ne, ne_eq, decide_eq_true_eq, hd3, not_false_eq_true, decide_true, Bool.and_self]
          simp only [hb, ↓reduceIte]
    constructor
    · rintro ⟨hup, hd1, hd2, hd3⟩
      unfold Engine.upperPoints _root_.Unicode.toUppercase _root_.Unicode.fullMapping at hup
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hup
      cases hs : _root_.Unicode.lookupSortedA _root_.Unicode.uppercaseSpecialA c' with
      | some m =>
        rw [hs] at hup
        have hm := hspOk.2.1 (c', m) ((lookupSortedA_iff _ hspSort c' m).1 hs)
        dsimp only at hm
        have hlen1 := congrArg List.length hup
        simp only [List.length_cons, List.length_nil] at hlen1
        unfold maxPoint at *; unfold maxCodePoint at *; omega
      | none =>
        rw [hs] at hup
        cases hrun : _root_.Unicode.lookupRunsA _root_.Unicode.uppercaseRunsA c' with
        | none =>
          have hle : decide (c' ≤ maxPoint) = true := decide_eq_true hc'
          simp [hrun, Option.ucdOrSelf, hle] at hup; cases hup; exact absurd rfl hd3
        | some d'' =>
          obtain ⟨r, hrm, hfc, hcl, _, rfl⟩ := (lookupRunsA_iff upperRuns_ok c' d'').1 hrun
          obtain ⟨_, _, _, hf0, hlmax, _⟩ := hbU r hrm
          have hle : decide (((c' : Int) + r.delta).toNat ≤ maxPoint) = true :=
            decide_eq_true (by unfold maxPoint; unfold maxCodePoint at *; omega)
          simp only [hrun, Option.ucdOrSelf, Option.getD_some, List.filter, hle, ↓reduceIte] at hup
          cases hup; exact hmem_run.2 ⟨hs, hd1, hd2, hd3, hrun⟩
    · intro hm; obtain ⟨hsN, hd1, hd2, hd3, hrun⟩ := hmem_run.1 hm
      refine ⟨?_, hd1, hd2, hd3⟩
      unfold Engine.upperPoints _root_.Unicode.toUppercase _root_.Unicode.fullMapping
      obtain ⟨r, hrm, hfc, hcl, _, rfl⟩ := (lookupRunsA_iff upperRuns_ok c' d').1 hrun
      obtain ⟨_, _, _, hf0, hlmax, _⟩ := hbU r hrm
      have hle : decide (((c' : Int) + r.delta).toNat ≤ maxPoint) = true :=
        decide_eq_true (by unfold maxPoint; unfold maxCodePoint at *; omega)
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hsN, hrun, Option.ucdOrSelf,
        Option.getD_some, List.filter, hle, ↓reduceIte]
  have hcanonEq : ∀ (ic : Bool), Model.canonChar Impl ic u (.int c) =
      if !ic then .int c
      else if u then match Engine.scfPoint? c with | some d => .int d | none => .int c
      else match Engine.upperPoints [c] with
        | [d] => if d ≤ 0xFFFF && !(128 ≤ c && d < 128) then .int d else .int c
        | _ => .int c := by
    intro ic; cases ic
    · rfl
    · cases u
      · rw [canonChar_true_false Impl (.int c), toUpper_single c, canonUpperBody_map_eval]; rfl
      · have hidx : MathVal.idx (.int c) = some c := rfl
        change (MathVal.idx (.int c) |>.bind fun n => Option.map (fun d : Nat => MathVal.int d) (Engine.scfPoint? n)).getD (.int c) = _
        rw [hidx]
        cases hsp : Engine.scfPoint? c <;> simp [hsp]
  constructor
  · cases u
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hcanonEq true]
      cases hu : Engine.upperPoints [c] with
      | nil => exact ⟨fun h => by cases h; exact .inr ⟨rfl, fun ⟨d', hd'⟩ => by have := (hnonU c d' hc).2 hd' |>.1; rw [hu] at this; cases this⟩, fun h => by rcases h with ⟨_, hd'⟩ | ⟨hdc, _⟩; have := (hnonU c _ hc).2 hd' |>.1; rw [hu] at this; cases this; exact hdc ▸ rfl⟩
      | cons x r =>
        cases r with
        | cons _ _ => exact ⟨fun h => by cases h; exact .inr ⟨rfl, fun ⟨d', hd'⟩ => by have := (hnonU c d' hc).2 hd' |>.1; rw [hu] at this; cases this⟩, fun h => by rcases h with ⟨_, hd'⟩ | ⟨hdc, _⟩; have := (hnonU c _ hc).2 hd' |>.1; rw [hu] at this; cases this; exact hdc ▸ rfl⟩
        | nil =>
          dsimp only; by_cases hcnd : (decide (x ≤ 0xFFFF) && !(decide (128 ≤ c) && decide (x < 128))) = true
          · simp only [hcnd, ↓reduceIte]
            have hb : decide (x ≤ 0xFFFF) = true ∧ (!(decide (128 ≤ c) && decide (x < 128))) = true :=
              (Bool.and_eq_true _ _).mp hcnd
            have hb2 : (!(128 ≤ c && x < 128)) = true := by
              by_cases h1' : 128 ≤ c <;> by_cases h2' : x < 128 <;> simp_all
            by_cases hxc : x = c
            · exact ⟨fun h => by
                have hxEq : x = d := by cases h; rfl
                exact .inr ⟨hxEq.symm.trans hxc, fun ⟨d', hd'⟩ => by
                  have hnu := (hnonU c d' hc).2 hd'
                  have h1 : x = d' := (List.cons.inj (hu ▸ hnu.1)).1
                  exact hnu.2.2.2 (h1.symm.trans hxc)⟩,
                fun h => by
                  rcases h with ⟨hne, hd'⟩ | ⟨hdc, _⟩
                  · have hnu := (hnonU c d hc).2 hd'
                    have h1 : x = d := (List.cons.inj (hu ▸ hnu.1)).1
                    exact absurd (h1.symm.trans hxc) hne
                  · rw [hxc, hdc]; rfl⟩
            · exact ⟨fun h => by
                have hxEq : x = d := by cases h; rfl
                subst hxEq
                exact .inl ⟨hxc, (hnonU c x hc).1 ⟨hu, of_decide_eq_true hb.1, hb2, hxc⟩⟩,
                fun h => by
                  rcases h with ⟨_, hd'⟩ | ⟨hdc, hnot⟩
                  · have hnu := (hnonU c d hc).2 hd'
                    have h1 : x = d := (List.cons.inj (hu ▸ hnu.1)).1
                    rw [h1]; rfl
                  · exact absurd ⟨x, (hnonU c x hc).1 ⟨hu, of_decide_eq_true hb.1, hb2, hxc⟩⟩ hnot⟩
          · simp only [hcnd, Bool.false_eq_true, ↓reduceIte]
            exact ⟨fun h => by cases h; exact .inr ⟨rfl, fun ⟨d', hd'⟩ => by
                have hnu := (hnonU c d' hc).2 hd'
                have h1 : x = d' := (List.cons.inj (hu ▸ hnu.1)).1
                have h21 := hnu.2.1; have h22 := hnu.2.2.1; rw [← h1] at h21 h22
                simp [h21, h22] at hcnd⟩,
              fun h => by
                rcases h with ⟨_, hd'⟩ | ⟨hdc, _⟩
                · have hnu := (hnonU c d hc).2 hd'
                  have h1 : x = d := (List.cons.inj (hu ▸ hnu.1)).1
                  have h21 := hnu.2.1; have h22 := hnu.2.2.1; rw [← h1] at h21 h22
                  simp [h21, h22] at hcnd
                · rw [hdc]; rfl⟩
    · simp only [↓reduceIte]; rw [hcanonEq true]
      cases hs : Engine.scfPoint? c with
      | none => exact ⟨fun h => by cases h; exact .inr ⟨rfl, fun ⟨d', hd'⟩ => by rw [(scfPoint?_iff_pairs hc d').2 hd'] at hs; cases hs⟩,
          fun h => by rcases h with ⟨_, hd'⟩ | ⟨hdc, _⟩; rw [(scfPoint?_iff_pairs hc _).2 hd'] at hs; cases hs; exact hdc ▸ rfl⟩
      | some d' =>
        have hmem := (scfPoint?_iff_pairs hc d').1 hs
        have hne : d' ≠ c := by
          obtain ⟨r, hrm, hx⟩ := List.mem_flatMap.1 (show (c, d') ∈ scfPairsList from hmem)
          obtain ⟨c', hc', heq⟩ := List.mem_map.1 hx; cases heq
          have hr := hbS r hrm
          simp only [hr.1, hr.2.1, and_self, ↓reduceIte] at hc'
          have hbc' := (runPointsFuel_mem _ _ _ _ hr.1 hr.2.1 (Nat.le_refl _) [] c).1 hc'
          have hcf : r.first ≤ c := by rcases hbc' with hnil | ⟨h1, _, _⟩; cases hnil; exact h1
          have := hr.2.2.2.2.2 rfl; omega
        exact ⟨fun h => by cases h; exact .inl ⟨hne, hmem⟩,
          fun h => by rcases h with ⟨_, hd''⟩ | ⟨hdc, hnot⟩; have := (scfPoint?_iff_pairs hc _).2 hd''; rw [hs] at this; cases this; rfl; exact absurd ⟨d', hmem⟩ hnot⟩
  · cases u <;> simp only [↓reduceIte, Bool.false_eq_true]
    · intro p hp
      obtain ⟨r, hrm, hx⟩ := List.mem_flatMap.1 hp
      obtain ⟨c', hc', hfm⟩ := List.mem_filterMap.1 hx
      have hr := hbU r hrm; simp only [hr.1, hr.2.1, and_self, ↓reduceIte] at hc'
      rcases (runPointsFuel_mem _ _ _ _ hr.1 hr.2.1 (Nat.le_refl _) [] c').1 hc' with h | ⟨_, h2, _⟩
      · cases h
      · cases hsl : _root_.Unicode.lookupSortedA _root_.Unicode.uppercaseSpecialA c' with
        | some _ => simp [hsl] at hfm
        | none =>
          rw [hsl] at hfm; dsimp only at hfm
          by_cases hcnd : (decide (((c' : Int) + r.delta).toNat ≤ 0xFFFF) && !(decide (128 ≤ c') && decide (((c' : Int) + r.delta).toNat < 128)) && (((c' : Int) + r.delta).toNat != c')) = true
          · simp only [hcnd, ↓reduceIte, Option.some.injEq] at hfm
            subst hfm
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hcnd
            exact ⟨by omega, by change ((c' : Int) + r.delta).toNat ≤ 0x10FFFF; omega, hcnd.2⟩
          · simp only [hcnd, Bool.false_eq_true, ↓reduceIte] at hfm; cases hfm
    · intro p hp
      obtain ⟨r, hrm, hx⟩ := List.mem_flatMap.1 hp
      obtain ⟨c', hc', heq⟩ := List.mem_map.1 hx; subst heq
      have hr := hbS r hrm; simp only [hr.1, hr.2.1, and_self, ↓reduceIte] at hc'
      rcases (runPointsFuel_mem _ _ _ _ hr.1 hr.2.1 (Nat.le_refl _) [] c').1 hc' with h | ⟨_, h2, _⟩
      · cases h
      · have := hr.2.2.2.2.2 rfl; omega

def LeDC (x y : Nat × Nat) : Prop := x.2 < y.2 ∨ (x.2 = y.2 ∧ x.1 ≤ y.1)

theorem mergePairsDCFuel_spec : ∀ (k : Nat) (xs ys : List (Nat × Nat)), xs.length + ys.length ≤ k →
    (mergePairsDCFuel k xs ys).length = xs.length + ys.length ∧
    (∀ p, p ∈ mergePairsDCFuel k xs ys ↔ p ∈ xs ∨ p ∈ ys) ∧
    (xs.Pairwise LeDC → ys.Pairwise LeDC → (mergePairsDCFuel k xs ys).Pairwise LeDC) := by
  intro k; induction k with
  | zero =>
    intro xs ys hk
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx; subst hy; simp [mergePairsDCFuel]
  | succ k ih =>
    intro xs ys hk
    cases xs with
    | nil => simp [mergePairsDCFuel]
    | cons x xs' =>
      cases ys with
      | nil => simp [mergePairsDCFuel]
      | cons y ys' =>
        unfold mergePairsDCFuel
        by_cases hcmp : (x.2 < y.2 || (x.2 == y.2 && x.1 ≤ y.1)) = true
        · have hle : LeDC x y := by simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcmp; exact hcmp
          have ⟨hlen, hmem, hpw⟩ := ih xs' (y :: ys') (by simp only [List.length_cons] at hk ⊢; omega)
          simp only [hcmp, ↓reduceIte, List.length_cons, List.mem_cons]
          refine ⟨by rw [hlen]; simp only [List.length_cons]; omega, fun p => by rw [hmem]; simp [or_left_comm, or_assoc], fun hpx hpy => ?_⟩
          obtain ⟨hxw, hxs⟩ := List.pairwise_cons.1 hpx
          obtain ⟨hyw, hys⟩ := List.pairwise_cons.1 hpy
          refine List.pairwise_cons.2 ⟨fun p hp => ?_, hpw hxs (List.pairwise_cons.2 ⟨hyw, hys⟩)⟩
          rcases (hmem p).1 hp with hp1 | hp2
          · exact hxw p hp1
          · rcases List.mem_cons.1 hp2 with rfl | hp3
            · exact hle
            · have := hyw p hp3; unfold LeDC at *; omega
        · have hle : LeDC y x := by
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcmp
            unfold LeDC; omega
          have ⟨hlen, hmem, hpw⟩ := ih (x :: xs') ys' (by simp only [List.length_cons] at hk ⊢; omega)
          simp only [hcmp, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.mem_cons]
          refine ⟨by rw [hlen]; simp only [List.length_cons]; omega, fun p => by rw [hmem]; simp [or_left_comm, or_assoc], fun hpx hpy => ?_⟩
          obtain ⟨hxw, hxs⟩ := List.pairwise_cons.1 hpx
          obtain ⟨hyw, hys⟩ := List.pairwise_cons.1 hpy
          refine List.pairwise_cons.2 ⟨fun p hp => ?_, hpw (List.pairwise_cons.2 ⟨hxw, hxs⟩) hys⟩
          rcases (hmem p).1 hp with hp1 | hp2
          · rcases List.mem_cons.1 hp1 with rfl | hp3
            · exact hle
            · have := hxw p hp3; unfold LeDC at *; omega
          · exact hyw p hp2

theorem mergePairsListDC_spec (n : Nat) : ∀ zs : List (List (Nat × Nat)), zs.length ≤ n →
    (∀ l ∈ zs, l.Pairwise LeDC) →
    (∀ l ∈ mergePairsListDC zs, l.Pairwise LeDC) ∧
    (∀ p, (∃ l ∈ mergePairsListDC zs, p ∈ l) ↔ ∃ l ∈ zs, p ∈ l) ∧
    (2 ≤ zs.length → (mergePairsListDC zs).length < zs.length) := by
  induction n with
  | zero =>
    intro zs hz _; have hnil : zs = [] := List.eq_nil_of_length_eq_zero (by omega); subst hnil
    simp [mergePairsListDC]
  | succ n ih =>
    intro zs hz hp
    cases zs with
    | nil => simp [mergePairsListDC]
    | cons a r =>
      cases r with
      | nil =>
        exact ⟨hp, fun _ => Iff.rfl, fun h2 => by simp at h2⟩
      | cons b zs' =>
        have ha : a.Pairwise LeDC := hp a (by simp)
        have hb : b.Pairwise LeDC := hp b (by simp)
        have ⟨hmLen, hmMem, hmPw⟩ := mergePairsDCFuel_spec (a.length + b.length + 1) a b (by omega)
        have ⟨ih1, ih2, ih3⟩ := ih zs' (by simp at hz; omega) fun l hl => hp l (by simp [hl])
        refine ⟨fun l hl => ?_, fun p => ?_, fun _ => ?_⟩
        · rcases List.mem_cons.1 hl with rfl | hl'
          · exact hmPw ha hb
          · exact ih1 l hl'
        · simp only [mergePairsListDC, List.mem_cons]
          constructor
          · rintro ⟨l, rfl | hl', hpl⟩
            · rcases (hmMem p).1 hpl with ha' | hb'; exact ⟨a, .inl rfl, ha'⟩; exact ⟨b, .inr (.inl rfl), hb'⟩
            · obtain ⟨l', hl'', hpl'⟩ := (ih2 p).1 ⟨l, hl', hpl⟩
              exact ⟨l', .inr (.inr hl''), hpl'⟩
          · rintro ⟨l, rfl | rfl | hl, hpl⟩
            · exact ⟨_, .inl rfl, (hmMem p).2 (.inl hpl)⟩
            · exact ⟨_, .inl rfl, (hmMem p).2 (.inr hpl)⟩
            · obtain ⟨l', hl', hpl'⟩ := (ih2 p).2 ⟨l, hl, hpl⟩
              exact ⟨l', .inr hl', hpl'⟩
        · simp only [mergePairsListDC, List.length_cons]
          by_cases hz2 : 2 ≤ zs'.length
          · have := ih3 hz2; omega
          · cases zs' with
            | nil => simp [mergePairsListDC]
            | cons c zs'' =>
              cases zs'' with
              | nil => simp [mergePairsListDC]
              | cons _ _ => simp at hz2

theorem sortPairsDC_spec (ps : List (Nat × Nat)) :
    (sortPairsDC ps).Pairwise LeDC ∧ ∀ p, p ∈ sortPairsDC ps ↔ p ∈ ps := by
  suffices ∀ (k : Nat) (zs : List (List (Nat × Nat))), zs.length ≤ k + 1 →
      (∀ l ∈ zs, l.Pairwise LeDC) →
      (sortPairsDCGo k zs).Pairwise LeDC ∧ ∀ p, p ∈ sortPairsDCGo k zs ↔ ∃ l ∈ zs, p ∈ l by
    have ⟨h1, h2⟩ := this ps.length (ps.map ([·])) (by simp) fun l hl => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 hl; exact List.pairwise_singleton _ _
    exact ⟨h1, fun p => (h2 p).trans ⟨fun ⟨l, hl, hp⟩ => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hl; cases List.mem_singleton.1 hp; exact hq,
      fun hp => ⟨[p], List.mem_map.2 ⟨p, hp, rfl⟩, by simp⟩⟩⟩
  intro k; induction k with
  | zero =>
    intro zs hz hp
    cases zs with
    | nil => simp [sortPairsDCGo]
    | cons a r =>
      cases r with
      | nil => simp [sortPairsDCGo, hp a (by simp)]
      | cons _ _ => simp at hz
  | succ k ih =>
    intro zs hz hp
    cases zs with
    | nil => simp [sortPairsDCGo]
    | cons a r =>
      cases r with
      | nil => simp [sortPairsDCGo, hp a (by simp)]
      | cons b zs' =>
        have ⟨hm1, hm2, hm3⟩ := mergePairsListDC_spec (a :: b :: zs').length (a :: b :: zs') (Nat.le_refl _) hp
        have hlt := hm3 (by simp)
        have ⟨ih1, ih2⟩ := ih (mergePairsListDC (a :: b :: zs')) (by simp only [List.length_cons] at hlt hz; omega) hm1
        simp only [sortPairsDCGo]
        exact ⟨ih1, fun p => (ih2 p).trans (hm2 p)⟩

theorem groupPre_spec (curD : Nat) (curCs : List Nat) (hasCur : Bool) (acc : List (Nat × Array Nat))
    (l : List (Nat × Nat)) (hl : l.Pairwise LeDC) (haccPw : acc.Pairwise fun a b => b.1 < a.1)
    (hnone : hasCur = false → acc = [] ∧ curCs = [])
    (hsome : hasCur = true → (∀ x ∈ acc, x.1 < curD) ∧ ∀ p ∈ l, curD ≤ p.2) :
    (groupPre curD curCs hasCur acc l).Pairwise (fun a b => a.1 < b.1) ∧
    ∀ c d, (∃ cs, (d, cs) ∈ groupPre curD curCs hasCur acc l ∧ c ∈ cs) ↔
      (d = curD ∧ hasCur = true ∧ c ∈ curCs) ∨ (∃ cs, (d, cs) ∈ acc ∧ c ∈ cs) ∨ (c, d) ∈ l := by
  induction l generalizing curD curCs hasCur acc with
  | nil =>
    unfold groupPre
    cases hasCur
    · obtain ⟨hacc, hcs⟩ := hnone rfl; subst hacc hcs
      simp [List.Pairwise.nil]
    · refine ⟨?_, fun c d => ?_⟩
      · exact List.pairwise_reverse.2 (List.pairwise_cons.2 ⟨(hsome rfl).1, haccPw⟩)
      · simp only [↓reduceIte, List.mem_reverse, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro ⟨cs, hcs, hmc⟩
          rcases hcs with hEq | hAcc
          · cases hEq; exact .inl ⟨rfl, trivial, by rw [← Array.mem_toList_iff] at hmc; simpa using hmc⟩
          · exact .inr ⟨cs, hAcc, hmc⟩
        · rintro (⟨rfl, _, hmc⟩ | ⟨cs, hAcc, hmc⟩)
          · exact ⟨curCs.reverse.toArray, .inl rfl, by rw [← Array.mem_toList_iff]; simpa using hmc⟩
          · exact ⟨cs, .inr hAcc, hmc⟩
  | cons p r ih =>
    rcases p with ⟨c', d'⟩
    obtain ⟨hpwR, hlR⟩ := List.pairwise_cons.1 hl
    have hgeR : ∀ q ∈ r, d' ≤ q.2 := fun q hq => by
      have := hpwR q hq; unfold LeDC at this; omega
    unfold groupPre
    cases hasCur
    · simp only [Bool.not_false, ↓reduceIte]
      obtain ⟨hacc, hcs⟩ := hnone rfl; subst hacc hcs
      have ⟨ihPw, ihMem⟩ := ih d' [c'] true [] hlR List.Pairwise.nil (fun h => by cases h) (fun _ => ⟨fun _ hm => (by cases hm), hgeR⟩)
      refine ⟨ihPw, fun c d => ?_⟩
      rw [ihMem c d]; simp only [Bool.false_eq_true, and_false, false_and, List.not_mem_nil,
        List.mem_cons, or_false, Prod.mk.injEq, false_or, exists_false]
      constructor
      · rintro (⟨rfl, _, rfl⟩ | h); exact .inl ⟨rfl, rfl⟩; exact .inr h
      · rintro (⟨rfl, rfl⟩ | h); exact .inl ⟨rfl, trivial, rfl⟩; exact .inr h
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hd : d' = curD
      · subst hd
        simp only [beq_self_eq_true, ↓reduceIte]
        let curCs' := if curCs.head? == some c' then curCs else c' :: curCs
        have hcurMem : ∀ x, x ∈ curCs' ↔ x = c' ∨ x ∈ curCs := fun x => by
          dsimp only [curCs']; cases hcHead : curCs.head? == some c'
          · simp
          · cases curCs with
            | nil => cases hcHead
            | cons h t =>
              simp only [List.head?_cons, beq_iff_eq, Option.some.injEq] at hcHead
              subst hcHead; simp only [List.mem_cons, ↓reduceIte]; constructor
              · rintro (rfl | ht); exact .inl rfl; exact .inr (.inr ht)
              · rintro (rfl | rfl | ht); exact .inl rfl; exact .inl rfl; exact .inr ht
        have ⟨ihPw, ihMem⟩ := ih d' curCs' true acc hlR haccPw (fun h => by cases h) fun _ => ⟨(hsome rfl).1, hgeR⟩
        refine ⟨ihPw, fun c d => ?_⟩
        rw [ihMem c d, hcurMem c]
        simp only [List.mem_cons, Prod.mk.injEq]
        constructor
        · rintro (⟨rfl, _, hEq | hCur⟩ | hAcc | hr)
          · exact .inr (.inr (.inl ⟨hEq, rfl⟩))
          · exact .inl ⟨rfl, trivial, hCur⟩
          · exact .inr (.inl hAcc)
          · exact .inr (.inr (.inr hr))
        · rintro (⟨rfl, _, hCur⟩ | hAcc | ⟨⟨rfl, rfl⟩ | hr⟩)
          · exact .inl ⟨rfl, trivial, .inr hCur⟩
          · exact .inr (.inl hAcc)
          · exact .inl ⟨rfl, trivial, .inl rfl⟩
          · exact .inr (.inr hr)
      · have hneB : (d' == curD) = false := beq_false_of_ne hd
        simp only [hneB, Bool.false_eq_true, ↓reduceIte]
        have hltD : curD < d' := by
          have := (hsome rfl).2 (c', d') (by simp); omega
        have haccPw' : ((curD, curCs.reverse.toArray) :: acc).Pairwise fun a b => b.1 < a.1 :=
          List.pairwise_cons.2 ⟨(hsome rfl).1, haccPw⟩
        have haccLt' : ∀ x ∈ (curD, curCs.reverse.toArray) :: acc, x.1 < d' := fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx'
          · exact hltD
          · exact Nat.lt_trans ((hsome rfl).1 x hx') hltD
        have ⟨ihPw, ihMem⟩ := ih d' [c'] true ((curD, curCs.reverse.toArray) :: acc) hlR haccPw' (fun h => by cases h) fun _ => ⟨haccLt', hgeR⟩
        refine ⟨ihPw, fun c d => ?_⟩
        rw [ihMem c d]
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
        constructor
        · rintro (⟨rfl, _, rfl⟩ | ⟨cs, ⟨rfl, rfl⟩ | hAcc, hmc⟩ | hr)
          · exact .inr (.inr (.inl ⟨rfl, rfl⟩))
          · exact .inl ⟨rfl, trivial, by rw [← Array.mem_toList_iff] at hmc; simpa using hmc⟩
          · exact .inr (.inl ⟨cs, hAcc, hmc⟩)
          · exact .inr (.inr (.inr hr))
        · rintro (⟨rfl, _, hCur⟩ | ⟨cs, hAcc, hmc⟩ | ⟨⟨rfl, rfl⟩ | hr⟩)
          · exact .inr (.inl ⟨curCs.reverse.toArray, .inl ⟨rfl, rfl⟩, by rw [← Array.mem_toList_iff]; simpa using hCur⟩)
          · exact .inr (.inl ⟨cs, .inr hAcc, hmc⟩)
          · exact .inl ⟨rfl, trivial, rfl⟩
          · exact .inr (.inr hr)

theorem buildPreimages_spec (pairsList : List (Nat × Nat)) (c d : Nat) :
    (c, d) ∈ pairsList ↔ ∃ cs, _root_.Unicode.lookupSortedA (buildPreimages pairsList) d = some cs ∧ c ∈ cs := by
  have ⟨hsPw, hsMem⟩ := sortPairsDC_spec pairsList
  have ⟨hgPw, hgMem⟩ := groupPre_spec 0 [] false [] (sortPairsDC pairsList) hsPw List.Pairwise.nil (fun _ => ⟨rfl, rfl⟩) fun h => by cases h
  let pre := buildPreimages pairsList
  have hprSort : ∀ i j (hi : i < pre.size) (hj : j < pre.size), i < j → pre[i].1 < pre[j].1 := fun i j hi hj hij => by
    have := List.pairwise_iff_getElem.1 hgPw i j (by simpa [pre, buildPreimages] using hi) (by simpa [pre, buildPreimages] using hj) hij
    simpa [pre, buildPreimages] using this
  constructor
  · intro hm
    obtain ⟨cs, hmemG, hcs⟩ := (hgMem c d).2 (.inr (.inr ((hsMem (c, d)).2 hm)))
    exact ⟨cs, (lookupSortedA_iff pre hprSort d cs).2 (by simpa [pre, buildPreimages] using hmemG), hcs⟩
  · rintro ⟨cs, hl, hcs⟩
    have hmemPre := (lookupSortedA_iff pre hprSort d cs).1 hl
    rcases (hgMem c d).1 ⟨cs, by simpa [pre, buildPreimages] using hmemPre, hcs⟩ with ⟨_, hf, _⟩ | ⟨_, hm, _⟩ | hIn
    · cases hf
    · cases hm
    · exact (hsMem (c, d)).1 hIn

theorem csHas_noScf_law (e : Array MathVal) (he : Model.allPoints Impl e) :
    Impl.csHas Impl.csNoScf e = true ↔
      ∃ c, seqList (M := Impl) e = [c] ∧ Model.isPoint Impl c ∧ (Impl.scf? c).getD c = c := by
  obtain ⟨pts, hmap⟩ := (allPoints_iff e).1 he
  have ⟨hl, hle⟩ := mapM_point?_eq hmap
  have hpairsSpec := (canonChar_pair_iff true (Nat.zero_le _) 0).2
  have ⟨_, hdomMem⟩ := coalescePoints_ok (scfPairsList.map Prod.fst)
    (List.pairwise_map.2 (pairsListOk_spec 0 scfPairsList scfPairs_listOk).2)
    (fun c hc => by obtain ⟨p, hm, rfl⟩ := List.mem_map.1 hc; exact (hpairsSpec p hm).1)
  have ⟨_, hcMem⟩ := complRanges_ok scfDomainRanges scfDomainRanges_ok
  rw [csHas_iff_mem _ pts hle hl]
  simp only [csNoScf, wmap_empty_get pts, Option.isSome_none, Bool.false_eq_true, and_false, or_false, seqList_eq, hl]
  simp only [hcMem]
  rw [show scfDomainRanges = coalescePoints (scfPairsList.map Prod.fst) from rfl]
  simp only [hdomMem, List.mem_map]
  constructor
  · rintro ⟨c, rfl, hcLe, hcNot⟩
    refine ⟨.int c, rfl, nat_isPoint c hcLe, ?_⟩
    have hnone : Engine.scfPoint? c = none := by
      cases hs : Engine.scfPoint? c with | none => rfl | some d => exact absurd ⟨(c, d), (scfPoint?_iff_pairs hcLe d).1 hs, rfl⟩ hcNot
    have hidx : MathVal.idx (.int c) = some c := rfl
    change ((MathVal.idx (.int c)).bind (fun n => Option.map (fun d : Nat => MathVal.int d) (Engine.scfPoint? n))).getD (.int c) = .int c
    rw [hidx]; simp [hnone]
  · rintro ⟨c, hce, hcPt, hscf⟩
    obtain ⟨cn, hcn, rfl⟩ := (isPoint_iff c).1 hcPt
    have hpts : pts = [cn] := int_map_inj (by simpa using hce); subst hpts
    refine ⟨cn, rfl, hcn, fun ⟨⟨c', d⟩, hm, heq'⟩ => ?_⟩
    dsimp only at heq'; rw [heq'] at hm
    have hidx : MathVal.idx (.int cn) = some cn := rfl
    change ((MathVal.idx (.int cn)).bind (fun n => Option.map (fun d : Nat => MathVal.int d) (Engine.scfPoint? n))).getD (.int cn) = .int cn at hscf
    rw [hidx] at hscf; simp [(scfPoint?_iff_pairs hcn d).2 hm] at hscf
    exact (hpairsSpec _ hm).2.2 (by cases hscf; rfl)

theorem csHas_canonExtra_law (cs : CharSet) (u : Bool) (e : Array MathVal) (he : Model.allPoints Impl e) :
    Impl.csHas (Impl.csCanonExtra cs u) e = true ↔
      ∃ c, seqList (M := Impl) e = [c] ∧ Model.isPoint Impl c ∧
        Impl.csHas cs (Impl.seqPush Impl.seqNil c) = false ∧
        Impl.csHas cs (Impl.seqPush Impl.seqNil (Model.canonChar Impl true u c)) = true := by
  obtain ⟨pts, hmap⟩ := (allPoints_iff e).1 he
  have ⟨hl, hle⟩ := mapM_point?_eq hmap
  let pairs := if u then scfPairs else nonUCanonPairs
  have hok : pairsListOk 0 pairs.toList = true := by cases u <;> simp [pairs, scfPairs, nonUCanonPairs, scfPairs_listOk, nonUCanonPairs_listOk]
  have ⟨_, hmemF⟩ := foldl_filter_pushRange_ok cs pairs.toList [] 0 hok trivial (Nat.zero_le _)
  have ⟨_, hrMem⟩ := revOk_reverse (foldl_filter_pushRange_ok cs pairs.toList [] 0 hok trivial (Nat.zero_le _)).1
  have hrEq : (csCanonExtra cs u).ranges.toList = (pairs.foldl (fun acc (c, d) =>
      if !csHasChar cs c && csHasChar cs d then pushRange acc c c else acc) []).reverse := by
    simp [csCanonExtra, pairs]
  rw [csHas_iff_mem _ pts hle hl, hrEq, ← Array.foldl_toList]
  simp only [hrMem, hmemF, memRanges_nil, false_or, csCanonExtra, wmap_empty_get pts,
    Option.isSome_none, Bool.false_eq_true, and_false, or_false, seqList_eq, hl]
  have hpairsMem : ∀ x, x ∈ pairs.toList ↔ x ∈ (if u then scfPairsList else nonUCanonPairsList) := by
    cases u <;> simp [pairs, scfPairs, nonUCanonPairs]
  have hasFalse : ∀ x (hx : x ≤ maxCodePoint), csHasChar cs x = false ↔ Impl.csHas cs (Impl.seqPush Impl.seqNil (.int x)) = false :=
    fun x hx => by rw [Bool.eq_false_iff, Bool.eq_false_iff, ne_eq, ne_eq, hasChar_iff cs x hx]
  constructor
  · rintro ⟨c, rfl, d, hdp, hc0, hd1⟩
    have hdp' := (hpairsMem (c, d)).1 hdp
    have ⟨hcLe, hdLe, hne⟩ := (canonChar_pair_iff u (Nat.zero_le _) 0).2 (c, d) hdp'
    have hcan := (canonChar_pair_iff u hcLe d).1.2 (.inl ⟨hne, hdp'⟩)
    refine ⟨.int c, rfl, nat_isPoint c hcLe, (hasFalse c hcLe).1 hc0, ?_⟩
    rw [hcan]; exact (hasChar_iff cs d hdLe).1 hd1
  · rintro ⟨c, hce, hcPt, hc0, hd1⟩
    obtain ⟨cn, hcn, rfl⟩ := (isPoint_iff c).1 hcPt
    have hpts : pts = [cn] := int_map_inj (by simpa using hce); subst hpts
    have hcanPt : Model.isPoint Impl (Model.canonChar Impl true u (.int cn)) := by
      cases u
      · rw [canonChar_true_false Impl (.int cn)]
        exact canonChar_upper_isPoint_gen cn hcn (Impl.toUpper (Impl.seqPush Impl.seqNil (.int cn)))
          (unicodeLaws.toUpper_points _ (by simpa using points_isPoint [cn] fun _ h => by simp at h; subst h; exact hcn))
      · change Model.isPoint Impl ((Impl.scf? (.int cn)).getD (.int cn))
        cases hsp : Impl.scf? (.int cn) with
        | none => exact nat_isPoint cn hcn
        | some d => exact unicodeLaws.scf_point (.int cn) d (nat_isPoint cn hcn) hsp
    obtain ⟨d, hdLe, hcan⟩ := (isPoint_iff _).1 hcanPt
    have hcanNe : d ≠ cn := fun h => by subst h; rw [hcan, hc0] at hd1; cases hd1
    rcases (canonChar_pair_iff u hcn d).1.1 hcan with ⟨_, hdp⟩ | ⟨rfl, _⟩
    · have hdp' := (hpairsMem (cn, d)).2 hdp
      exact ⟨cn, rfl, d, hdp', (hasFalse cn hcn).2 hc0, (hasChar_iff cs d hdLe).2 (hcan ▸ hd1)⟩
    · exact absurd rfl hcanNe

theorem csHasCanon_iff_law (cs : CharSet) (cc : MathVal) (u ic : Bool) (hcc : Model.isPoint Impl cc) :
    Impl.csHasCanon cs cc u ic = true ↔
      ∃ a, Model.isPoint Impl a ∧ Impl.csHas cs (Impl.seqPush Impl.seqNil a) = true ∧
        Model.canonChar Impl ic u a = cc := by
  obtain ⟨c, hc, rfl⟩ := (isPoint_iff cc).1 hcc
  change Engine.Model.csHasCanon cs (.int c) u ic = true ↔ _
  unfold Engine.Model.csHasCanon
  rw [(point?_eq_some (.int c) c).2 ⟨hc, rfl⟩]
  cases ic
  · constructor
    · intro h; exact ⟨.int c, nat_isPoint c hc, (hasChar_iff cs c hc).1 h, by simp [Model.canonChar]⟩
    · rintro ⟨a, haPt, haHas, haCan⟩
      obtain ⟨an, han, rfl⟩ := (isPoint_iff a).1 haPt
      simp only [Model.canonChar, Bool.not_false, ↓reduceIte] at haCan
      have hanEq : an = c := by cases haCan; rfl
      subst hanEq; exact (hasChar_iff cs an han).2 haHas
  · let pre := if u then scfPreimages else nonUCanonPreimages
    let dom := if u then scfDomainRanges else nonUCanonDomainRanges
    let plist := if u then scfPairsList else nonUCanonPairsList
    have hEqPre : (if u then (scfPreimages, scfDomainRanges) else (nonUCanonPreimages, nonUCanonDomainRanges)).1 = pre := by
      cases u <;> rfl
    have hEqDom : (if u then (scfPreimages, scfDomainRanges) else (nonUCanonPreimages, nonUCanonDomainRanges)).2 = dom := by
      cases u <;> rfl
    have hPreBuild : pre = buildPreimages plist := by cases u <;> rfl
    have hpairsSpec := (canonChar_pair_iff u hc 0).2
    have hdomOk : rangeListOk 0 dom.toList = true ∧ ∀ x, MemRanges dom.toList x ↔ ∃ d, (x, d) ∈ plist := by
      have hpaList : pairsListOk 0 plist = true := by cases u <;> simp [plist, scfPairs_listOk, nonUCanonPairs_listOk]
      have ⟨hk, hm⟩ := coalescePoints_ok (plist.map Prod.fst) (List.pairwise_map.2 (pairsListOk_spec 0 plist hpaList).2)
        (fun x hx => by obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hx; exact (hpairsSpec p hpm).1)
      have hdomEq : dom = coalescePoints (plist.map Prod.fst) := by cases u <;> rfl
      rw [hdomEq]; exact ⟨hk, fun x => (hm x).trans (by simp [List.mem_map])⟩
    dsimp only
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hEqPre, hEqDom]
    constructor
    · intro h
      cases hl : _root_.Unicode.lookupSortedA pre c with
      | some as =>
        rw [hl] at h; dsimp only at h
        by_cases h1 : as.any (csHasChar cs) = true
        · obtain ⟨k, hk, haHas⟩ := Array.any_eq_true.1 h1
          have hpair := (buildPreimages_spec plist as[k] c).2 ⟨as, hPreBuild ▸ hl, Array.getElem_mem hk⟩
          have ⟨haLe, _, hne⟩ := hpairsSpec _ hpair
          exact ⟨.int as[k], nat_isPoint as[k] haLe, (hasChar_iff cs as[k] haLe).1 haHas, (canonChar_pair_iff u haLe c).1.2 (.inl ⟨hne, hpair⟩)⟩
        · have h1f : as.any (csHasChar cs) = false := Bool.eq_false_iff.2 h1
          rw [h1f, Bool.false_or] at h
          have hdom : _root_.Unicode.inRangesA dom c = false := by cases hd : _root_.Unicode.inRangesA dom c <;> simp_all
          have hhas : csHasChar cs c = true := by simp_all
          have hnotDom : ¬ ∃ d, (c, d) ∈ plist := fun hm =>
            absurd ((inRangesA_iff dom hdomOk.1 c).2 ((hdomOk.2 c).2 hm)) (by simp [hdom])
          exact ⟨.int c, nat_isPoint c hc, (hasChar_iff cs c hc).1 hhas, (canonChar_pair_iff u hc c).1.2 (.inr ⟨rfl, hnotDom⟩)⟩
      | none =>
        rw [hl] at h; dsimp only at h
        have hdom : _root_.Unicode.inRangesA dom c = false := by cases hd : _root_.Unicode.inRangesA dom c <;> simp_all
        have hhas : csHasChar cs c = true := by simp_all
        have hnotDom : ¬ ∃ d, (c, d) ∈ plist := fun hm =>
          absurd ((inRangesA_iff dom hdomOk.1 c).2 ((hdomOk.2 c).2 hm)) (by simp [hdom])
        exact ⟨.int c, nat_isPoint c hc, (hasChar_iff cs c hc).1 hhas, (canonChar_pair_iff u hc c).1.2 (.inr ⟨rfl, hnotDom⟩)⟩
    · rintro ⟨a, haPt, haHas, haCan⟩
      obtain ⟨an, han, rfl⟩ := (isPoint_iff a).1 haPt
      rcases (canonChar_pair_iff u han c).1.1 (by simpa using haCan) with ⟨hne, hpair⟩ | ⟨rfl, hnotDom⟩
      · obtain ⟨as, hl, ham⟩ := (buildPreimages_spec plist an c).1 hpair
        obtain ⟨k, hk, hEq⟩ := Array.mem_iff_getElem.1 ham
        have hany : as.any (csHasChar cs) = true := Array.any_eq_true.2 ⟨k, hk, hEq ▸ (hasChar_iff cs an han).2 haHas⟩
        have hlPre : _root_.Unicode.lookupSortedA pre c = some as := hPreBuild ▸ hl
        rw [hlPre]; simp [hany]
      · have hdomF : _root_.Unicode.inRangesA dom c = false := by
          rw [Bool.eq_false_iff, ne_eq, inRangesA_iff dom hdomOk.1 c, hdomOk.2 c]; exact hnotDom
        have hright : (!_root_.Unicode.inRangesA dom c && csHasChar cs c) = true := by
          simp [hdomF, (hasChar_iff cs c hc).2 haHas]
        rw [hright]; simp

end Engine.Impl
