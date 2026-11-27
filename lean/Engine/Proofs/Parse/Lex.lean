module

public import Engine.Parse.Lex
public import Engine.Proofs.Parse.Code
public import Ecma.Grammar.Gen.Lexical1
public import Ecma.Grammar.Gen.Lexical2
public import Ecma.Grammar.Gen.AnnexB

@[expose] public section

open Ecma.Grammar
open Engine.Parse
open Engine.Parse.Search

namespace Engine.Parse

/-! ## Basic option / except / array / slice helpers -/

private theorem opt_none_or_some {α : Type} (o : Option α) :
    o = none ∨ ∃ x, o = some x := by
  cases o with
  | none => exact Or.inl rfl
  | some x => exact Or.inr ⟨x, rfl⟩

private theorem except_eq_err_or_ok {ε α : Type} (r : Except ε α) :
    (∃ e, r = .error e) ∨ (∃ v, r = .ok v) := by
  cases r with
  | error e => exact Or.inl ⟨e, rfl⟩
  | ok v => exact Or.inr ⟨v, rfl⟩

theorem codePointsOf_le_max {src : Array Engine.Model.MathVal} {cs : Array Nat}
    (h : Engine.codePointsOf src = some cs) :
    ∀ c ∈ cs.toList, c ≤ 0x10FFFF := by
  unfold Engine.codePointsOf at h
  have hlist : ∀ (xs : List Engine.Model.MathVal) (ys : List Nat),
      (xs.mapM fun | .int i => if 0 ≤ i ∧ i ≤ 0x10FFFF then some i.toNat else none | _ => none) = some ys →
      ∀ c ∈ ys, c ≤ 0x10FFFF := by
    intro xs
    induction xs with
    | nil =>
      intro ys hm c hc
      simp only [List.mapM_nil, pure, Option.some.injEq] at hm
      subst hm; cases hc
    | cons x rest ih =>
      intro ys hm c hc
      simp only [List.mapM_cons, Bind.bind, Option.bind] at hm
      cases x with
      | int i =>
        dsimp only at hm
        by_cases hi : 0 ≤ i ∧ i ≤ 0x10FFFF
        · simp only [hi, and_self, ↓reduceIte] at hm
          rcases opt_none_or_some (rest.mapM fun | .int i => if 0 ≤ i ∧ i ≤ 0x10FFFF then some i.toNat else none | _ => none) with hn | ⟨tl, htl⟩
          · rw [hn] at hm; cases hm
          · rw [htl] at hm
            simp only [pure, Option.some.injEq] at hm
            subst hm
            rcases List.mem_cons.mp hc with rfl | hmem
            · omega
            · exact ih tl htl c hmem
        · simp only [hi, ↓reduceIte] at hm; cases hm
      | _ => cases hm
  have hmapM : (src.toList.mapM fun | .int i => if 0 ≤ i ∧ i ≤ 0x10FFFF then some i.toNat else none | _ => none) = some cs.toList := by
    rw [← Array.toList_mapM]
    exact congrArg (Option.map Array.toList) h
  exact hlist src.toList cs.toList hmapM

theorem extract_codePoints_le_max {cs : Array Nat} (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF)
    (a b : Nat) : ∀ c ∈ (cs.extract a b).toList, c ≤ 0x10FFFF := by
  intro c hc
  rw [extract_toList_eq_slice] at hc
  unfold slice at hc
  exact hcp c (List.mem_of_mem_drop (List.mem_of_mem_take hc))

/-! ## Character classes (`isLT`, `isWS`, `lineTerminators`, `idStart`) -/

def ltCodePoints : List Nat := [0xA, 0xD, 0x2028, 0x2029]

def uspCodePoints : List Nat :=
  [0x20, 0xA0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004,
   0x2005, 0x2006, 0x2007, 0x2008, 0x2009, 0x200A, 0x202F, 0x205F, 0x3000]

def wsCodePoints : List Nat := [0x9, 0xB, 0xC, 0xFEFF] ++ uspCodePoints

theorem lineTerminators_eq : lineTerminators = [0xA, 0xD, 0x2028, 0x2029] := by decide

theorem isLT_iff_mem (c : Nat) : Lex.isLT c = true ↔ c ∈ ltCodePoints := by
  simp only [Lex.isLT, ltCodePoints, Bool.or_eq_true, beq_iff_eq, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem isLT_eq_contains (c : Nat) : Lex.isLT c = lineTerminators.contains c := by
  rw [lineTerminators_eq]
  apply Bool.eq_iff_iff.mpr
  rw [isLT_iff_mem, List.contains_iff_mem]
  rfl

theorem usp_iff_mem (c : Nat) : Engine.builder.usp c = true ↔ c ∈ uspCodePoints := by
  show Unicode.spaceSeparator c = true ↔ c ∈ uspCodePoints
  unfold Unicode.spaceSeparator Unicode.spaceSeparatorRanges uspCodePoints
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem isWS_iff_mem (c : Nat) : Lex.isWS Engine.builder c = true ↔ c ∈ wsCodePoints := by
  unfold Lex.isWS wsCodePoints
  simp only [Bool.or_eq_true, beq_iff_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, usp_iff_mem]
  simp only [or_assoc]

private theorem ws_lt_disjoint_cert : (wsCodePoints.all fun c => !Lex.isLT c) = true := by decide

theorem isWS_not_isLT {c : Nat} (h : Lex.isWS Engine.builder c = true) : Lex.isLT c = false := by
  have hm := (isWS_iff_mem c).mp h
  have ha := List.all_eq_true.mp ws_lt_disjoint_cert c hm
  simpa using ha

private theorem not_inClassRanges {t : Array (Nat × Nat)} {c : Nat}
    (hout : ∀ p ∈ t.toList, c < p.1 ∨ p.2 < c) :
    Unicode.inClassRanges t c = false := by
  unfold Unicode.inClassRanges
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  let stepFn : Nat → Option Bool × Nat × Nat → Id (ForInStep (Option Bool × Nat × Nat)) :=
    fun _ s =>
      if s.2.1 ≥ s.2.2 then pure (.done (none, s.2.1, s.2.2))
      else
        if c < t[(s.2.1 + s.2.2) / 2]!.1 then pure (.yield (none, s.2.1, (s.2.1 + s.2.2) / 2))
        else if t[(s.2.1 + s.2.2) / 2]!.2 < c then pure (.yield (none, (s.2.1 + s.2.2) / 2 + 1, s.2.2))
        else pure (.done (some true, s.2.1, s.2.2))
  have hloop : ∀ (xs : List Nat) (lo hi : Nat), hi ≤ t.size →
      ∃ lo' hi', Id.run (forIn (m := Id) xs (none, lo, hi) stepFn) = (none, lo', hi') := by
    intro xs
    induction xs with
    | nil => intro lo hi _; exact ⟨lo, hi, rfl⟩
    | cons _ rest ih =>
      intro lo hi hhi
      simp only [List.forIn_cons]
      dsimp only [stepFn]
      by_cases hge : lo ≥ hi
      · simp only [hge, ↓reduceIte]
        exact ⟨lo, hi, rfl⟩
      · simp only [hge, ↓reduceIte]
        have hmid : (lo + hi) / 2 < t.size := by omega
        have hbang : t[(lo + hi) / 2]! = t[(lo + hi) / 2] := getElem!_pos t ((lo + hi) / 2) hmid
        rw [hbang]
        have hmem : t[(lo + hi) / 2] ∈ t.toList := Array.mem_toList_iff.mpr (Array.getElem_mem hmid)
        rcases hout t[(lo + hi) / 2] hmem with hlt | hgt
        · simp only [hlt, ↓reduceIte]
          exact ih lo ((lo + hi) / 2) (by omega)
        · by_cases hlt : c < t[(lo + hi) / 2].1
          · simp only [hlt, ↓reduceIte]
            exact ih lo ((lo + hi) / 2) (by omega)
          · simp only [hlt, ↓reduceIte, hgt]
            exact ih ((lo + hi) / 2 + 1) hi hhi
  obtain ⟨lo', hi', heq⟩ := hloop (List.range' ([:64] : Std.Legacy.Range).start ([:64] : Std.Legacy.Range).size ([:64] : Std.Legacy.Range).step) 0 t.size (Nat.le_refl _)
  dsimp only [stepFn] at heq
  dsimp only [Id.run, Bind.bind, Monad.toBind, Id.instMonad, pure] at heq ⊢
  rw [heq]

private def nonIdStartList : List Nat :=
  wsCodePoints ++ ltCodePoints ++ [0x21, 0x23, 0x2D, 0x2F, 0x3C]

set_option maxRecDepth 10000 in
private theorem nonIdStart_cert :
    (Unicode.idStartRanges.all fun p =>
      decide (0x41 ≤ p.1) &&
      (decide (0xA0 < p.1) || decide (p.2 < 0xA0)) &&
      (decide (0x1680 < p.1) || decide (p.2 < 0x1680)) &&
      (decide (0x205F < p.1) || decide (p.2 < 0x2000)) &&
      (decide (0x3000 < p.1) || decide (p.2 < 0x3000)) &&
      (decide (0xFEFF < p.1) || decide (p.2 < 0xFEFF))) = true := by
  decide

private theorem nonIdStart_in_gaps :
    (nonIdStartList.all fun c =>
      decide (c < 0x41) || decide (c = 0xA0) || decide (c = 0x1680) ||
      (decide (0x2000 ≤ c) && decide (c ≤ 0x205F)) ||
      decide (c = 0x3000) || decide (c = 0xFEFF)) = true := by
  decide

private theorem nonIdStart_of_mem {c : Nat} (h : c ∈ nonIdStartList) :
    Engine.builder.idStart c = false := by
  show Unicode.idStart c = false
  unfold Unicode.idStart Unicode.idStartTable
  simp only [Thunk.get]
  apply not_inClassRanges
  intro p hp
  rw [List.toList_toArray] at hp
  have hp' := List.all_eq_true.mp nonIdStart_cert p hp
  have hc' := List.all_eq_true.mp nonIdStart_in_gaps c h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp' hc'
  omega

theorem isWS_not_idStart {c : Nat} (h : Lex.isWS Engine.builder c = true) :
    Engine.builder.idStart c = false :=
  nonIdStart_of_mem (List.mem_append_left _ (List.mem_append_left _ ((isWS_iff_mem c).mp h)))

theorem isLT_not_idStart {c : Nat} (h : Lex.isLT c = true) :
    Engine.builder.idStart c = false :=
  nonIdStart_of_mem (List.mem_append_left _ (List.mem_append_right _ ((isLT_iff_mem c).mp h)))

private theorem ws_not_comment_delim_cert :
    (wsCodePoints.all fun c =>
      c != 0x2F && c != 0x2D && c != 0x23 && c != 0x3C && c != 0x24 && c != 0x5F && c != 0x5C) = true := by
  decide

private theorem lt_not_comment_delim_cert :
    (ltCodePoints.all fun c =>
      c != 0x2F && c != 0x2A && c != 0x2D && c != 0x23 && c != 0x3C && c != 0x24 && c != 0x5F && c != 0x5C) = true := by
  decide

theorem isWS_ne {c : Nat} (h : Lex.isWS Engine.builder c = true) :
    c ≠ 0x2F ∧ c ≠ 0x2D ∧ c ≠ 0x23 ∧ c ≠ 0x3C ∧ c ≠ 0x24 ∧ c ≠ 0x5F ∧ c ≠ 0x5C := by
  have ha := List.all_eq_true.mp ws_not_comment_delim_cert c ((isWS_iff_mem c).mp h)
  simp only [Bool.and_eq_true, bne_iff_ne] at ha
  exact ⟨ha.1.1.1.1.1.1, ha.1.1.1.1.1.2, ha.1.1.1.1.2, ha.1.1.1.2, ha.1.1.2, ha.1.2, ha.2⟩

theorem isLT_ne {c : Nat} (h : Lex.isLT c = true) :
    c ≠ 0x2F ∧ c ≠ 0x2A ∧ c ≠ 0x2D ∧ c ≠ 0x23 ∧ c ≠ 0x3C ∧ c ≠ 0x24 ∧ c ≠ 0x5F ∧ c ≠ 0x5C := by
  have ha := List.all_eq_true.mp lt_not_comment_delim_cert c ((isLT_iff_mem c).mp h)
  simp only [Bool.and_eq_true, bne_iff_ne] at ha
  exact ⟨ha.1.1.1.1.1.1.1, ha.1.1.1.1.1.1.2, ha.1.1.1.1.1.2, ha.1.1.1.1.2, ha.1.1.1.2, ha.1.1.2, ha.1.2, ha.2⟩

/-! ## `lineEnd`, `closeAt`, `wsEnd`, and `extract` / `slice` line-terminator equivalence -/

theorem lineEnd_spec (cs : Array Nat) (k : Nat) :
    min k cs.size ≤ Lex.lineEnd cs k ∧
    Lex.lineEnd cs k ≤ cs.size ∧
    (∀ p, k ≤ p → p < Lex.lineEnd cs k → ∃ c, cs[p]? = some c ∧ Lex.isLT c = false) ∧
    (Lex.lineEnd cs k < cs.size → ∃ c, cs[Lex.lineEnd cs k]? = some c ∧ Lex.isLT c = true) := by
  by_cases hk : k < cs.size
  · cases hlt : Lex.isLT cs[k] with
    | true =>
      have heq : Lex.lineEnd cs k = k := by rw [Lex.lineEnd.eq_1]; simp [hk, hlt]
      rw [heq]
      refine ⟨Nat.min_le_left _ _, Nat.le_of_lt hk, (fun p hp1 hp2 => by omega), (fun _ => ⟨cs[k], Array.getElem?_eq_getElem hk, hlt⟩)⟩
    | false =>
      have heq : Lex.lineEnd cs k = Lex.lineEnd cs (k + 1) := by rw [Lex.lineEnd.eq_1]; simp [hk, hlt]
      have ⟨ih1, ih2, ih3, ih4⟩ := lineEnd_spec cs (k + 1)
      rw [heq]
      have hmin : min k cs.size ≤ min (k + 1) cs.size := by omega
      refine ⟨Nat.le_trans hmin ih1, ih2, ?_, ih4⟩
      intro p hp1 hp2
      by_cases hpk : p = k
      · subst hpk; exact ⟨cs[p], Array.getElem?_eq_getElem hk, hlt⟩
      · exact ih3 p (by omega) hp2
  · have heq : Lex.lineEnd cs k = cs.size := by rw [Lex.lineEnd.eq_1]; simp [hk]
    rw [heq]
    exact ⟨Nat.min_le_right _ _, Nat.le_refl _, (fun p hp1 hp2 => by omega), (fun h => by omega)⟩
termination_by cs.size - k

theorem lineEnd_ge_of_le (cs : Array Nat) {k : Nat} (hk : k ≤ cs.size) :
    k ≤ Lex.lineEnd cs k := by
  have ⟨h1, _⟩ := lineEnd_spec cs k
  rwa [Nat.min_eq_left hk] at h1

theorem closeAt_some_spec (cs : Array Nat) : ∀ (k c : Nat),
    Lex.closeAt cs k = some c →
    k ≤ c ∧ c + 1 < cs.size ∧ cs[c]? = some 0x2A ∧ cs[c + 1]? = some 0x2F ∧
    ∀ p, k ≤ p → p < c → ¬(cs[p]? = some 0x2A ∧ cs[p + 1]? = some 0x2F) := by
  intro k c h
  unfold Lex.closeAt at h
  by_cases hk : k + 1 < cs.size
  · simp only [hk, ↓reduceDIte] at h
    by_cases hm : (cs[k] == 0x2A && cs[k + 1] == 0x2F) = true
    · simp only [hm, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      have hk0 : k < cs.size := by omega
      exact ⟨Nat.le_refl _, hk, by rw [Array.getElem?_eq_getElem hk0, hm.1],
        by rw [Array.getElem?_eq_getElem hk, hm.2], fun p hp1 hp2 => by omega⟩
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
      have ⟨ih1, ih2, ih3, ih4, ih5⟩ := closeAt_some_spec cs (k + 1) c h
      refine ⟨by omega, ih2, ih3, ih4, ?_⟩
      intro p hp1 hp2
      by_cases hpk : p = k
      · subst hpk
        rintro ⟨ha, hb⟩
        have hk0 : p < cs.size := by omega
        rw [Array.getElem?_eq_getElem hk0, Option.some.injEq] at ha
        rw [Array.getElem?_eq_getElem hk, Option.some.injEq] at hb
        simp [ha, hb] at hm
      · exact ih5 p (by omega) hp2
  · simp only [hk, ↓reduceDIte] at h; cases h
termination_by k => cs.size - k

theorem closeAt_none_spec (cs : Array Nat) : ∀ (k : Nat),
    Lex.closeAt cs k = none →
    ∀ p, k ≤ p → p + 1 < cs.size → ¬(cs[p]? = some 0x2A ∧ cs[p + 1]? = some 0x2F) := by
  intro k h
  unfold Lex.closeAt at h
  by_cases hk : k + 1 < cs.size
  · simp only [hk, ↓reduceDIte] at h
    by_cases hm : (cs[k] == 0x2A && cs[k + 1] == 0x2F) = true
    · simp [hm] at h
    · simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
      have ih := closeAt_none_spec cs (k + 1) h
      intro p hp1 hp2
      by_cases hpk : p = k
      · subst hpk
        rintro ⟨ha, hb⟩
        have hk0 : p < cs.size := by omega
        rw [Array.getElem?_eq_getElem hk0, Option.some.injEq] at ha
        rw [Array.getElem?_eq_getElem hk, Option.some.injEq] at hb
        simp [ha, hb] at hm
      · exact ih p (by omega) hp2
  · intro p hp1 hp2; omega
termination_by k => cs.size - k

theorem wsEnd_spec (cs : Array Nat) (k : Nat) :
    k ≤ Lex.wsEnd Engine.builder cs k ∧
    (k ≤ cs.size → Lex.wsEnd Engine.builder cs k ≤ cs.size) ∧
    (∀ p, k ≤ p → p < Lex.wsEnd Engine.builder cs k → ∃ c, cs[p]? = some c ∧ Lex.isWS Engine.builder c = true) ∧
    (Lex.wsEnd Engine.builder cs k < cs.size → ∃ c, cs[Lex.wsEnd Engine.builder cs k]? = some c ∧ Lex.isWS Engine.builder c = false) := by
  by_cases hk : k < cs.size
  · cases hws : Lex.isWS Engine.builder cs[k] with
    | false =>
      have heq : Lex.wsEnd Engine.builder cs k = k := by rw [Lex.wsEnd.eq_1]; simp [hk, hws]
      rw [heq]
      exact ⟨Nat.le_refl _, (fun _ => Nat.le_of_lt hk), (fun p hp1 hp2 => by omega),
        (fun _ => ⟨cs[k], Array.getElem?_eq_getElem hk, hws⟩)⟩
    | true =>
      have heq : Lex.wsEnd Engine.builder cs k = Lex.wsEnd Engine.builder cs (k + 1) := by rw [Lex.wsEnd.eq_1]; simp [hk, hws]
      have ⟨ih1, ih2, ih3, ih4⟩ := wsEnd_spec cs (k + 1)
      rw [heq]
      refine ⟨by omega, (fun _ => ih2 (by omega)), ?_, ih4⟩
      intro p hp1 hp2
      by_cases hpk : p = k
      · subst hpk; exact ⟨cs[p], Array.getElem?_eq_getElem hk, hws⟩
      · exact ih3 p (by omega) hp2
  · have heq : Lex.wsEnd Engine.builder cs k = k := by rw [Lex.wsEnd.eq_1]; simp [hk]
    rw [heq]
    exact ⟨Nat.le_refl _, (fun hle => hle), (fun p hp1 hp2 => by omega), (fun hlt => absurd hlt hk)⟩
termination_by cs.size - k

theorem slice_any_lt_eq_extract (cs : Array Nat) (a b : Nat) :
    (slice cs.toList a b).any lineTerminators.contains = (cs.extract a b).any Lex.isLT := by
  rw [← extract_toList_eq_slice, ← Array.any_toList]
  congr 1
  funext c
  exact (isLT_eq_contains c).symm

theorem slice_mem_iff_index {α : Type} (xs : List α) {a b : Nat} (hb : b ≤ xs.length) (x : α) :
    x ∈ slice xs a b ↔ ∃ p, a ≤ p ∧ p < b ∧ xs[p]? = some x := by
  unfold slice
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨idx, hidx, hget⟩
    rw [List.length_take, List.length_drop] at hidx
    rw [List.getElem_take, List.getElem_drop] at hget
    refine ⟨a + idx, by omega, by omega, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), hget]
  · rintro ⟨p, hap, hpb, hpget⟩
    obtain ⟨hplen, rfl⟩ := List.getElem?_eq_some_iff.mp hpget
    refine ⟨p - a, ?_, ?_⟩
    · rw [List.length_take, List.length_drop]; omega
    · rw [List.getElem_take, List.getElem_drop]
      congr 1; omega

theorem extract_any_isLT_iff (cs : Array Nat) {a b : Nat} (hb : b ≤ cs.size) :
    (cs.extract a b).any Lex.isLT = true ↔ ∃ p c, a ≤ p ∧ p < b ∧ cs[p]? = some c ∧ Lex.isLT c = true := by
  rw [← slice_any_lt_eq_extract, List.any_eq_true]
  have hbl : b ≤ cs.toList.length := by simpa using hb
  constructor
  · rintro ⟨c, hcMem, hcLt⟩
    obtain ⟨p, hap, hpb, hpget⟩ := (slice_mem_iff_index cs.toList hbl c).mp hcMem
    exact ⟨p, c, hap, hpb, by simpa using hpget, by rw [isLT_eq_contains]; exact hcLt⟩
  · rintro ⟨p, c, hap, hpb, hpget, hcLt⟩
    refine ⟨c, (slice_mem_iff_index cs.toList hbl c).mpr ⟨p, hap, hpb, by simpa using hpget⟩, ?_⟩
    rw [← isLT_eq_contains]; exact hcLt

/-! ## Context reduction for `.lexical` (`cxHtmlFalse`, `cxHtmlTrue`) -/

def cxHtmlFalse : Ctx := ⟨true, {}⟩
def cxHtmlTrue : Ctx := ⟨false, { html := true }⟩

private def lexOverlayBlocksOk : Bool :=
  glData.blocks.all fun b =>
    match b.kind with
    | .overlay sec _ cond => !(overlayGrammar sec == .lexical) || (sec == .htmlLikeComments && cond == .notModule)
    | _ => true

private theorem lexOverlayBlocksOk_true : lexOverlayBlocksOk = true := by decide

private theorem beq_htmlLikeComments (s : AnnexB) :
    (s == .htmlLikeComments) = true ↔ s = .htmlLikeComments := by
  cases s <;> constructor <;> intro h <;> cases h <;> rfl

private theorem beq_notModule (c : OverlayCond) :
    (c == .notModule) = true ↔ c = .notModule := by
  cases c <;> constructor <;> intro h <;> cases h <;> rfl

private theorem filterMap_eq_nil_of_none {α β : Type} {f : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = none) → xs.filterMap f = []
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x List.mem_cons_self,
      filterMap_eq_nil_of_none (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.filterMap f = xs.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem overlays_lexical_eq (cx : Ctx) :
    glData.overlays cx .lexical =
      glData.overlays (if Lex.html cx then cxHtmlTrue else cxHtmlFalse) .lexical := by
  cases hhtml : Lex.html cx with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hfalse : glData.overlays cxHtmlFalse .lexical = [] := rfl
    rw [hfalse]
    unfold GL.overlays
    by_cases hany : (!cx.annexB.any) = true
    · simp [hany]
    · simp only [hany, Bool.false_eq_true, ↓reduceIte]
      apply filterMap_eq_nil_of_none
      intro b hb
      have hbok := List.all_eq_true.mp lexOverlayBlocksOk_true b hb
      cases hbk : b.kind with
      | main | supplemental _ => rfl
      | overlay sec md cd =>
        rw [hbk] at hbok
        dsimp only at hbok ⊢
        by_cases hog : (overlayGrammar sec == .lexical) = true
        · simp only [hog, Bool.not_true, Bool.false_or, Bool.and_eq_true,
            beq_htmlLikeComments, beq_notModule] at hbok
          rcases hbok with ⟨rfl, rfl⟩
          have hh0 : (cx.annexB.has .htmlLikeComments && condHolds cx .notModule) = false := hhtml
          simp [hog, hh0]
        · simp [hog]
  | true =>
    simp only [↓reduceIte]
    have hhc : cx.annexB.html = true ∧ cx.module = false := by
      unfold Lex.html AnnexB.Set.has at hhtml
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hhtml
      exact hhtml
    have hany1 : (!cx.annexB.any) = false := by
      unfold AnnexB.Set.any; simp [hhc.1]
    have hany2 : (!cxHtmlTrue.annexB.any) = false := rfl
    unfold GL.overlays
    rw [hany1, hany2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply filterMap_congr_mem
    intro b hb
    have hbok := List.all_eq_true.mp lexOverlayBlocksOk_true b hb
    cases hbk : b.kind with
    | main | supplemental _ => rfl
    | overlay sec md cd =>
      rw [hbk] at hbok
      dsimp only at hbok ⊢
      by_cases hog : (overlayGrammar sec == .lexical) = true
      · simp only [hog, Bool.not_true, Bool.false_or, Bool.and_eq_true,
          beq_htmlLikeComments, beq_notModule] at hbok
        rcases hbok with ⟨rfl, rfl⟩
        simp [AnnexB.Set.has, condHolds, hhc.1, hhc.2, cxHtmlTrue]
      · simp [hog]

theorem alts_lexical_eq (cx : Ctx) (n : NT) :
    Ecma.Spec.gl.alts cx .lexical n =
      glData.alts (if Lex.html cx then cxHtmlTrue else cxHtmlFalse) .lexical n := by
  rw [← glData_eq]
  unfold GL.alts
  rw [overlays_lexical_eq cx]

/-! ## Concrete alternative lists for lexical nonterminals (closed `decide` certificates) -/

private theorem alts_cert_core :
    glData.alts cxHtmlFalse .lexical .InputElementDiv = srcsOf .lexical Gen.Lexical.InputElementDiv ∧
    glData.alts cxHtmlTrue .lexical .InputElementDiv = srcsOf .lexical Gen.Lexical.InputElementDiv ∧
    glData.alts cxHtmlFalse .lexical .InputElementRegExp = srcsOf .lexical Gen.Lexical.InputElementRegExp ∧
    glData.alts cxHtmlTrue .lexical .InputElementRegExp = srcsOf .lexical Gen.Lexical.InputElementRegExp ∧
    glData.alts cxHtmlFalse .lexical .InputElementRegExpOrTemplateTail = srcsOf .lexical Gen.Lexical.InputElementRegExpOrTemplateTail ∧
    glData.alts cxHtmlTrue .lexical .InputElementRegExpOrTemplateTail = srcsOf .lexical Gen.Lexical.InputElementRegExpOrTemplateTail ∧
    glData.alts cxHtmlFalse .lexical .InputElementTemplateTail = srcsOf .lexical Gen.Lexical.InputElementTemplateTail ∧
    glData.alts cxHtmlTrue .lexical .InputElementTemplateTail = srcsOf .lexical Gen.Lexical.InputElementTemplateTail ∧
    glData.alts cxHtmlFalse .lexical .InputElementHashbangOrRegExp = srcsOf .lexical Gen.Lexical.InputElementHashbangOrRegExp ∧
    glData.alts cxHtmlTrue .lexical .InputElementHashbangOrRegExp =
      srcsOf .lexical Gen.Lexical.InputElementHashbangOrRegExp ++
      [⟨.annexB, Gen.AnnexB.InputElementHashbangOrRegExp, 6, ⟨[], [.sym (.nt .HTMLCloseComment []) false], none⟩⟩] := by
  decide

private theorem alts_cert_trivia :
    glData.alts cxHtmlFalse .lexical .SourceCharacter = srcsOf .lexical Gen.Lexical.SourceCharacter ∧
    glData.alts cxHtmlTrue .lexical .SourceCharacter = srcsOf .lexical Gen.Lexical.SourceCharacter ∧
    glData.alts cxHtmlFalse .lexical .WhiteSpace = srcsOf .lexical Gen.Lexical.WhiteSpace ∧
    glData.alts cxHtmlTrue .lexical .WhiteSpace = srcsOf .lexical Gen.Lexical.WhiteSpace ∧
    glData.alts cxHtmlFalse .lexical .LineTerminator = srcsOf .lexical Gen.Lexical.LineTerminator ∧
    glData.alts cxHtmlTrue .lexical .LineTerminator = srcsOf .lexical Gen.Lexical.LineTerminator ∧
    glData.alts cxHtmlFalse .lexical .LineTerminatorSequence = srcsOf .lexical Gen.Lexical.LineTerminatorSequence ∧
    glData.alts cxHtmlTrue .lexical .LineTerminatorSequence = srcsOf .lexical Gen.Lexical.LineTerminatorSequence ∧
    glData.alts cxHtmlFalse .lexical .Comment = srcsOf .lexical Gen.Lexical.Comment ∧
    glData.alts cxHtmlTrue .lexical .Comment =
      srcsOf .lexical Gen.Lexical.Comment ++ (srcsOf .annexB Gen.AnnexB.Comment).drop 2 ∧
    glData.alts cxHtmlFalse .lexical .MultiLineComment = srcsOf .lexical Gen.Lexical.MultiLineComment ∧
    glData.alts cxHtmlTrue .lexical .MultiLineComment =
      srcsOf .lexical Gen.Lexical.MultiLineComment ++ srcsOf .annexB Gen.AnnexB.MultiLineComment ∧
    glData.alts cxHtmlFalse .lexical .MultiLineCommentChars = srcsOf .lexical Gen.Lexical.MultiLineCommentChars ∧
    glData.alts cxHtmlTrue .lexical .MultiLineCommentChars = srcsOf .lexical Gen.Lexical.MultiLineCommentChars ∧
    glData.alts cxHtmlFalse .lexical .PostAsteriskCommentChars = srcsOf .lexical Gen.Lexical.PostAsteriskCommentChars ∧
    glData.alts cxHtmlTrue .lexical .PostAsteriskCommentChars = srcsOf .lexical Gen.Lexical.PostAsteriskCommentChars ∧
    glData.alts cxHtmlFalse .lexical .MultiLineNotAsteriskChar = srcsOf .lexical Gen.Lexical.MultiLineNotAsteriskChar ∧
    glData.alts cxHtmlTrue .lexical .MultiLineNotAsteriskChar = srcsOf .lexical Gen.Lexical.MultiLineNotAsteriskChar ∧
    glData.alts cxHtmlFalse .lexical .MultiLineNotForwardSlashOrAsteriskChar = srcsOf .lexical Gen.Lexical.MultiLineNotForwardSlashOrAsteriskChar ∧
    glData.alts cxHtmlTrue .lexical .MultiLineNotForwardSlashOrAsteriskChar = srcsOf .lexical Gen.Lexical.MultiLineNotForwardSlashOrAsteriskChar ∧
    glData.alts cxHtmlFalse .lexical .SingleLineComment = srcsOf .lexical Gen.Lexical.SingleLineComment ∧
    glData.alts cxHtmlTrue .lexical .SingleLineComment = srcsOf .lexical Gen.Lexical.SingleLineComment ∧
    glData.alts cxHtmlFalse .lexical .SingleLineCommentChars = srcsOf .lexical Gen.Lexical.SingleLineCommentChars ∧
    glData.alts cxHtmlTrue .lexical .SingleLineCommentChars = srcsOf .lexical Gen.Lexical.SingleLineCommentChars ∧
    glData.alts cxHtmlFalse .lexical .SingleLineCommentChar = srcsOf .lexical Gen.Lexical.SingleLineCommentChar ∧
    glData.alts cxHtmlTrue .lexical .SingleLineCommentChar = srcsOf .lexical Gen.Lexical.SingleLineCommentChar ∧
    glData.alts cxHtmlFalse .lexical .HashbangComment = srcsOf .lexical Gen.Lexical.HashbangComment ∧
    glData.alts cxHtmlTrue .lexical .HashbangComment = srcsOf .lexical Gen.Lexical.HashbangComment := by
  decide

private theorem alts_cert_annexB :
    glData.alts cxHtmlFalse .lexical .HTMLCloseComment = [] ∧
    glData.alts cxHtmlTrue .lexical .HTMLCloseComment = srcsOf .annexB Gen.AnnexB.HTMLCloseComment ∧
    glData.alts cxHtmlTrue .lexical .FirstCommentLine = srcsOf .annexB Gen.AnnexB.FirstCommentLine ∧
    glData.alts cxHtmlTrue .lexical .SingleLineHTMLOpenComment = srcsOf .annexB Gen.AnnexB.SingleLineHTMLOpenComment ∧
    glData.alts cxHtmlTrue .lexical .SingleLineHTMLCloseComment = srcsOf .annexB Gen.AnnexB.SingleLineHTMLCloseComment ∧
    glData.alts cxHtmlTrue .lexical .SingleLineDelimitedComment = srcsOf .annexB Gen.AnnexB.SingleLineDelimitedComment ∧
    glData.alts cxHtmlTrue .lexical .SingleLineDelimitedCommentChars = srcsOf .annexB Gen.AnnexB.SingleLineDelimitedCommentChars ∧
    glData.alts cxHtmlTrue .lexical .SingleLineNotAsteriskChar = srcsOf .annexB Gen.AnnexB.SingleLineNotAsteriskChar ∧
    glData.alts cxHtmlTrue .lexical .SingleLinePostAsteriskCommentChars = srcsOf .annexB Gen.AnnexB.SingleLinePostAsteriskCommentChars ∧
    glData.alts cxHtmlTrue .lexical .SingleLineNotForwardSlashOrAsteriskChar = srcsOf .annexB Gen.AnnexB.SingleLineNotForwardSlashOrAsteriskChar ∧
    glData.alts cxHtmlTrue .lexical .WhiteSpaceSequence = srcsOf .annexB Gen.AnnexB.WhiteSpaceSequence ∧
    glData.alts cxHtmlTrue .lexical .SingleLineDelimitedCommentSequence = srcsOf .annexB Gen.AnnexB.SingleLineDelimitedCommentSequence := by
  decide

private theorem alts_cert_tokens :
    glData.alts cxHtmlFalse .lexical .CommonToken = srcsOf .lexical Gen.Lexical.CommonToken ∧
    glData.alts cxHtmlTrue .lexical .CommonToken = srcsOf .lexical Gen.Lexical.CommonToken ∧
    glData.alts cxHtmlFalse .lexical .Template = srcsOf .lexical Gen.Lexical.Template ∧
    glData.alts cxHtmlTrue .lexical .Template = srcsOf .lexical Gen.Lexical.Template ∧
    glData.alts cxHtmlFalse .lexical .TemplateSubstitutionTail = srcsOf .lexical Gen.Lexical.TemplateSubstitutionTail ∧
    glData.alts cxHtmlTrue .lexical .TemplateSubstitutionTail = srcsOf .lexical Gen.Lexical.TemplateSubstitutionTail ∧
    glData.alts cxHtmlFalse .lexical .IdentifierStart = srcsOf .lexical Gen.Lexical.IdentifierStart ∧
    glData.alts cxHtmlTrue .lexical .IdentifierStart = srcsOf .lexical Gen.Lexical.IdentifierStart ∧
    glData.alts cxHtmlFalse .lexical .IdentifierStartChar = srcsOf .lexical Gen.Lexical.IdentifierStartChar ∧
    glData.alts cxHtmlTrue .lexical .IdentifierStartChar = srcsOf .lexical Gen.Lexical.IdentifierStartChar ∧
    glData.alts cxHtmlFalse .lexical .UnicodeIDStart = srcsOf .lexical Gen.Lexical.UnicodeIDStart ∧
    glData.alts cxHtmlTrue .lexical .UnicodeIDStart = srcsOf .lexical Gen.Lexical.UnicodeIDStart ∧
    glData.alts cxHtmlFalse .lexical .UnicodeEscapeSequence = srcsOf .lexical Gen.Lexical.UnicodeEscapeSequence ∧
    glData.alts cxHtmlTrue .lexical .UnicodeEscapeSequence = srcsOf .lexical Gen.Lexical.UnicodeEscapeSequence ∧
    glData.alts cxHtmlFalse .lexical .DecimalDigit = srcsOf .lexical Gen.Lexical.DecimalDigit ∧
    glData.alts cxHtmlTrue .lexical .DecimalDigit = srcsOf .lexical Gen.Lexical.DecimalDigit ∧
    glData.alts cxHtmlFalse .lexical .DivPunctuator = srcsOf .lexical Gen.Lexical.DivPunctuator ∧
    glData.alts cxHtmlTrue .lexical .DivPunctuator = srcsOf .lexical Gen.Lexical.DivPunctuator ∧
    glData.alts cxHtmlFalse .lexical .RightBracePunctuator = srcsOf .lexical Gen.Lexical.RightBracePunctuator ∧
    glData.alts cxHtmlTrue .lexical .RightBracePunctuator = srcsOf .lexical Gen.Lexical.RightBracePunctuator := by
  decide

private theorem alts_fixed_eq {cx : Ctx} {n : NT} {rs : List Src}
    (hf : glData.alts cxHtmlFalse .lexical n = rs)
    (ht : glData.alts cxHtmlTrue .lexical n = rs) :
    Ecma.Spec.gl.alts cx .lexical n = rs := by
  rw [alts_lexical_eq cx n]
  cases Lex.html cx with
  | false => exact hf
  | true => exact ht

private theorem alts_html_true_eq {cx : Ctx} {n : NT} {rs : List Src}
    (hhtml : Lex.html cx = true) (ht : glData.alts cxHtmlTrue .lexical n = rs) :
    Ecma.Spec.gl.alts cx .lexical n = rs := by
  rw [alts_lexical_eq cx n, hhtml]; exact ht

private theorem alts_html_false_eq {cx : Ctx} {n : NT} {rs : List Src}
    (hhtml : Lex.html cx = false) (hf : glData.alts cxHtmlFalse .lexical n = rs) :
    Ecma.Spec.gl.alts cx .lexical n = rs := by
  rw [alts_lexical_eq cx n, hhtml]; exact hf

/-! ## Bridge between `Derives ... .lexical` and `codeAlphaSpec ... .lexical` -/

abbrev LexDerives (cx : Ctx) (cs : Array Nat) (n : NT) (ps : List Param) (i j : Nat) (t : Tree) : Prop :=
  Derives Ecma.Spec.gl cx .lexical (codeAlphabet Engine.Model.codePrims) cs.toList n ps i j t

abbrev lexSpec (cs : Array Nat) (cx : Ctx) :
    AlphaSpec Engine.builder (Code.alpha (T := Unit) Engine.builder cs .lexical cx) cs.size :=
  codeAlphaSpec (T := Unit) Engine.builder cs .lexical cx 0 cs none

private theorem lexTerm_eq {cs : Array Nat} {cx : Ctx} {s : Src} {k : Nat} {t : Terminal} {i j : Nat}
    (h : (lexSpec cs cx).Term s k t i j) :
    Code.termEnd Engine.builder cs t i = some j := h

theorem lexical_mem_codeGrammars : GrammarId.lexical ∈ codeGrammars := by simp [codeGrammars]

theorem orderedBy_lexical_false (hok : parseTablesOk = true) (cx : Ctx) :
    orderedBy cx .lexical = false := by
  cases h : orderedBy cx .lexical with
  | false => rfl
  | true => exact nomatch (orderedBy_true_imp_regExp hok h)

theorem lexDerives_le (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {n : NT} {ps : List Param} {i j : Nat} {t : Tree}
    (hd : LexDerives cx cs n ps i j t) : i ≤ j := by
  obtain ⟨K, hK⟩ := hd
  have hst := hK (max K 1) (Nat.le_max_left K 1)
  obtain ⟨k0, hk0⟩ : ∃ k0, max K 1 = k0 + 1 := ⟨max K 1 - 1, by omega⟩
  rw [hk0] at hst
  exact code_step_le hok hst

theorem lexPlain_to_derives (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {n : NT} {ps : List Param} {i j : Nat} {dt : DTree}
    (hi : i ≤ cs.size)
    (hpl : (lexSpec cs cx).PlainDerives n ps i j dt) :
    i ≤ j ∧ j ≤ cs.size ∧ LexDerives cx cs n ps i j dt.toTree :=
  derivesWith_to_derives hok lexical_mem_codeGrammars codePrimsMatch_engine (condMatch_none cs) hi hpl

theorem lexDerives_to_plain (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {n : NT} {ps : List Param} {i j : Nat} {t : Tree}
    (hj : j ≤ cs.size)
    (hd : LexDerives cx cs n ps i j t) :
    ∃ dt, dt.toTree = t ∧ (lexSpec cs cx).PlainDerives n ps i j dt :=
  derives_to_plainDerives hok lexical_mem_codeGrammars codePrimsMatch_engine (condMatch_none cs) hj hd

theorem lexMode_iff_plain (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {n : NT} {ps : List Param} {i j : Nat} {dt : DTree} (hi : i ≤ cs.size) :
    (lexSpec cs cx).ModeDerives true n ps i j dt ↔ (lexSpec cs cx).PlainDerives n ps i j dt := by
  constructor
  · exact (lexSpec cs cx).derivesWith_mono_allow (fun _ _ _ _ _ => trivial)
  · intro hpl
    exact plain_and_commits_to_modeDerives hok lexical_mem_codeGrammars codePrimsMatch_engine
      (condMatch_none cs) hi hpl (fun ho => by rw [orderedBy_lexical_false hok cx] at ho; cases ho)

private theorem lex_mem_alts (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat} {n : NT} {s : Src}
    (hs : s ∈ altsOf (Code.alpha (T := Unit) Engine.builder cs .lexical cx).cx
      (Code.alpha (T := Unit) Engine.builder cs .lexical cx).g n) :
    s ∈ Ecma.Spec.gl.alts cx .lexical n := by
  dsimp only [Code.alpha] at hs
  rwa [altsOf_eq hok] at hs

private theorem lexSeqWith_le (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {a b : Nat} {m : List Bool} {ts : List DTree}
    (ha : a ≤ cs.size)
    (hsw : (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) s ps k is a b m ts) :
    a ≤ b ∧ b ≤ cs.size := by
  induction is generalizing k a m ts with
  | nil =>
    cases hsw
    exact ⟨Nat.le_refl _, ha⟩
  | cons it rest ih =>
    cases hsw with
    | absent hr => exact ih ha hr
    | term ht hr =>
      have hb := codeTerm_bound Engine.builder cs _ _ _ ht
      have ⟨h1, h2⟩ := ih hb.2 hr
      exact ⟨Nat.le_trans (Nat.le_of_lt hb.1) h1, h2⟩
    | nt _ hd _ _ hr =>
      have ⟨h0, hsz, _⟩ := lexPlain_to_derives hok ha hd
      have ⟨h1, h2⟩ := ih hsz hr
      exact ⟨Nat.le_trans h0 h1, h2⟩
    | leaf _ hl _ _ _ => exact nomatch hl
    | butNotT ht _ hr =>
      have hb := codeTerm_bound Engine.builder cs _ _ _ ht
      have ⟨h1, h2⟩ := ih hb.2 hr
      exact ⟨Nat.le_trans (Nat.le_of_lt hb.1) h1, h2⟩
    | butNotN _ hd _ _ hr =>
      have ⟨h0, hsz, _⟩ := lexPlain_to_derives hok ha hd
      have ⟨h1, h2⟩ := ih hsz hr
      exact ⟨Nat.le_trans h0 h1, h2⟩
    | butNotLeaf _ hl _ _ _ => exact nomatch hl
    | phrase hph hr =>
      obtain ⟨c, hcGet, _, rfl⟩ := hph
      have hsz : a + 1 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hcGet).1; omega
      have ⟨h1, h2⟩ := ih hsz hr
      exact ⟨by omega, h2⟩
    | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ih ha hr

private theorem mem_of_get? {α : Type} {xs : List α} (idx : Nat) {x : α} (h : xs[idx]? = some x) : x ∈ xs := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.getElem_mem hlt

private theorem mem_alts_of_get? {cx : Ctx} {n : NT} {rs : List Src}
    (h : Ecma.Spec.gl.alts cx .lexical n = rs) (idx : Nat) {x : Src} (hg : rs[idx]? = some x) :
    x ∈ Ecma.Spec.gl.alts cx .lexical n := by
  rw [h]; exact mem_of_get? idx hg

private theorem mkLexPlainSimple (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {n : NT} {ps : List Param} {i j : Nat} {s : Src} {m : List Bool} {kids : List DTree}
    (hs : s ∈ Ecma.Spec.gl.alts cx .lexical n)
    (hgrd : s.alt.guard.all (Guard.holds ps) = true)
    (hsw : (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) s ps 0 s.alt.rhs i j m kids) :
    ∃ id, (lexSpec cs cx).PlainDerives n ps i j (.node n id s ps i j m kids) := by
  obtain ⟨_, hopts⟩ := alt_lhs_and_opts hok hs
  obtain ⟨hpeq, id, _, hid, _⟩ := prodIdOf_spec hok hs (hopts ▸ (lexSpec cs cx).seqWith_masks hsw)
  have hsA : s ∈ altsOf (Code.alpha (T := Unit) Engine.builder cs .lexical cx).cx
      (Code.alpha (T := Unit) Engine.builder cs .lexical cx).g n := by
    dsimp only [Code.alpha]; rwa [altsOf_eq hok]
  exact ⟨id, .node s hsA trivial hgrd (hpeq.trans hid) hsw⟩

private theorem altsOf_nonempty_of_mem {cx : Ctx} {n : NT} {s : Src}
    (hok : parseTablesOk = true) (hs : s ∈ Ecma.Spec.gl.alts cx .lexical n) :
    (altsOf cx .lexical n).isEmpty = false := by
  rw [altsOf_eq hok]
  cases h : Ecma.Spec.gl.alts cx .lexical n with
  | nil => rw [h] at hs; cases hs
  | cons _ _ => rfl

private theorem altsOf_nonempty_of_srcs1 (hok : parseTablesOk = true) {cx : Ctx} {n : NT} {rs : List Src}
    (h : Ecma.Spec.gl.alts cx .lexical n = rs) (hne : rs.isEmpty = false) :
    (altsOf cx .lexical n).isEmpty = false := by
  rw [altsOf_eq hok, h]; exact hne

/-! ## Token prefix bounds (ruling out token overrides of trivia) -/

def allTokClasses : List NT :=
  [.IdentifierName, .PrivateIdentifier, .Punctuator, .NumericLiteral, .StringLiteral,
   .NoSubstitutionTemplate, .TemplateHead, .DivPunctuator, .RightBracePunctuator,
   .RegularExpressionLiteral, .TemplateMiddle, .TemplateTail]

private def tokLeadNTs : List NT :=
  allTokClasses ++
  [.IdentifierStart, .IdentifierStartChar, .UnicodeIDStart,
   .OptionalChainingPunctuator, .OtherPunctuator,
   .DecimalLiteral, .DecimalBigIntegerLiteral, .NonDecimalIntegerLiteral, .LegacyOctalIntegerLiteral,
   .DecimalIntegerLiteral, .DecimalDigit, .NonZeroDigit, .NonOctalDecimalIntegerLiteral,
   .BinaryIntegerLiteral, .OctalIntegerLiteral, .HexIntegerLiteral]

private def tokLeadAltOk (n : NT) (s : Src) : Bool :=
  match s.alt.rhs with
  | .sym (.t (.text str _)) false :: rest =>
    match str.toList.map Char.toNat with
    | [] => false
    | c0 :: csRest =>
      c0 < 0x80 && c0 != 0x20 && c0 != 0x9 && c0 != 0xB && c0 != 0xC && !Lex.isLT c0 &&
      (!(n == .IdentifierName || n == .IdentifierStart || n == .IdentifierStartChar || n == .UnicodeIDStart) ||
        (c0 == 0x24 || c0 == 0x5F || c0 == 0x5C)) &&
      (!(n != .DivPunctuator && n != .RegularExpressionLiteral) || c0 != 0x2F) &&
      (!(n != .Punctuator && n != .OtherPunctuator) || (c0 != 0x3C && c0 != 0x2D)) &&
      (if c0 == 0x2F then
        (n == .DivPunctuator && rest.isEmpty && (csRest == [] || csRest == [0x3D])) ||
        (n == .RegularExpressionLiteral && csRest == [] &&
          match rest with
          | .sym (.nt .RegularExpressionBody []) false :: _ => true
          | _ => false)
       else if c0 == 0x23 then
        n == .PrivateIdentifier && csRest == [] &&
          match rest with
          | [.sym (.nt .IdentifierName []) false] => true
          | _ => false
       else if c0 == 0x3C then
        rest.isEmpty && (csRest == [] || csRest == [0x3D] || csRest == [0x3C] || csRest == [0x3C, 0x3D])
       else if c0 == 0x2D then
        rest.isEmpty && (csRest == [] || csRest == [0x2D] || csRest == [0x3D])
       else true)
  | .sym (.nt m _) false :: rest =>
    tokLeadNTs.contains m &&
    n != .DivPunctuator && n != .RegularExpressionLiteral && n != .OtherPunctuator &&
    m != .DivPunctuator && m != .RegularExpressionLiteral && m != .PrivateIdentifier && m != .Punctuator &&
    (if n == .Punctuator then
       rest.isEmpty && (m == .OptionalChainingPunctuator || m == .OtherPunctuator)
     else if n == .IdentifierName || n == .IdentifierStart || n == .IdentifierStartChar || n == .UnicodeIDStart then
       m == .IdentifierName || m == .IdentifierStart || m == .IdentifierStartChar || m == .UnicodeIDStart
     else
       m != .OtherPunctuator && m != .OptionalChainingPunctuator &&
       m != .IdentifierName && m != .IdentifierStart && m != .IdentifierStartChar && m != .UnicodeIDStart)
  | [.phrase .idStart] =>
    n == .UnicodeIDStart
  | _ => false

private def tokLeadCert : Bool :=
  tokLeadNTs.all fun n =>
    (glData.alts cxHtmlFalse .lexical n).all (tokLeadAltOk n) &&
    (glData.alts cxHtmlTrue .lexical n).all (tokLeadAltOk n)

private theorem tokLeadCert_true : tokLeadCert = true := by decide

private theorem ascii_not_ws {c : Nat} (h80 : c < 0x80) (h20 : c ≠ 0x20)
    (h9 : c ≠ 0x9) (hb : c ≠ 0xB) (hc : c ≠ 0xC) :
    Lex.isWS Engine.builder c = false := by
  rw [Bool.eq_false_iff, ne_eq, isWS_iff_mem]
  unfold wsCodePoints uspCodePoints
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem termEnd_text_cons {cs : Array Nat} {str : String} {b : Bool} {k h : Nat} {c0 : Nat} {csRest : List Nat}
    (hw : str.toList.map Char.toNat = c0 :: csRest)
    (ht : Code.termEnd Engine.builder cs (.text str b) k = some h) :
    h = k + 1 + csRest.length ∧ cs[k]? = some c0 ∧
    (∀ c1 r1, csRest = c1 :: r1 → cs[k + 1]? = some c1) := by
  unfold Code.termEnd at ht
  dsimp only at ht
  rw [hw] at ht
  by_cases hc : (0 < (c0 :: csRest).length && k + (c0 :: csRest).length ≤ cs.size &&
      (cs.extract k (k + (c0 :: csRest).length)).toList == c0 :: csRest) = true
  · simp only [hc, ↓reduceIte, Option.some.injEq] at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.length_cons] at hc
    simp only [List.length_cons] at ht
    obtain ⟨⟨_, hle⟩, hex⟩ := hc
    rw [extract_toList_eq_slice] at hex
    have hkLt : k < cs.toList.length := by rw [Array.length_toList]; omega
    have hg0 : cs[k]? = some c0 := by
      have hhead : (slice cs.toList k (k + (csRest.length + 1))).head? = some c0 := by rw [hex]; rfl
      unfold slice at hhead
      rw [Nat.add_sub_cancel_left, List.drop_eq_getElem_cons hkLt, List.take_succ_cons,
        List.head?_cons, Option.some.injEq] at hhead
      rw [Array.getElem?_eq_getElem (by omega), Option.some.injEq]
      simpa using hhead
    refine ⟨by omega, hg0, ?_⟩
    intro c1 r1 hr1
    subst hr1
    simp only [List.length_cons] at ht hle hex
    have hk1Lt : k + 1 < cs.toList.length := by rw [Array.length_toList]; omega
    have htail : (slice cs.toList k (k + (r1.length + 1 + 1))).tail.head? = some c1 := by rw [hex]; rfl
    unfold slice at htail
    rw [Nat.add_sub_cancel_left, List.drop_eq_getElem_cons hkLt, List.take_succ_cons, List.tail_cons,
      List.drop_eq_getElem_cons hk1Lt, List.take_succ_cons, List.head?_cons, Option.some.injEq] at htail
    rw [Array.getElem?_eq_getElem (by omega), Option.some.injEq]
    simpa using htail
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at ht; cases ht

private theorem isEmpty_eq_true_iff {α : Type} {xs : List α} : xs.isEmpty = true ↔ xs = [] := by
  cases xs <;> simp

private theorem extract_one_at {cs : Array Nat} {i c : Nat} (h : cs[i]? = some c) :
    i + 1 ≤ cs.size ∧ (cs.extract i (i + 1)).toList = [c] := by
  have hi : i < cs.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [Array.getElem?_eq_getElem hi, Option.some.injEq] at h
  subst h
  refine ⟨by omega, ?_⟩
  rw [extract_toList_eq_slice]
  unfold slice
  have hiL : i < cs.toList.length := by rw [Array.length_toList]; exact hi
  rw [Nat.add_sub_cancel_left, List.drop_eq_getElem_cons hiL, List.take_succ_cons, List.take_zero]
  rfl

private theorem termEnd_text_mk {cs : Array Nat} (str : String) (b : Bool) (i : Nat)
    (hw : str.toList.map Char.toNat ≠ [])
    (hle : i + (str.toList.map Char.toNat).length ≤ cs.size)
    (hex : (cs.extract i (i + (str.toList.map Char.toNat).length)).toList = str.toList.map Char.toNat) :
    Code.termEnd Engine.builder cs (.text str b) i = some (i + (str.toList.map Char.toNat).length) := by
  unfold Code.termEnd
  dsimp only
  have hpos : 0 < (str.toList.map Char.toNat).length := List.length_pos_iff.mpr hw
  simp only [List.length_map] at hpos hle hex ⊢
  rw [hex]
  simp [hpos, hle]

private theorem reBody_not_slash_or_star (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {k h : Nat} {dt : DTree}
    (hc : cs[k]? = some 0x2F ∨ cs[k]? = some 0x2A)
    (hd : (lexSpec cs cx).PlainDerives .RegularExpressionBody [] k h dt) : False := by
  have haltsBody : glData.alts cxHtmlFalse .lexical .RegularExpressionBody = srcsOf .lexical Gen.Lexical.RegularExpressionBody ∧
      glData.alts cxHtmlTrue .lexical .RegularExpressionBody = srcsOf .lexical Gen.Lexical.RegularExpressionBody ∧
      glData.alts cxHtmlFalse .lexical .RegularExpressionFirstChar = srcsOf .lexical Gen.Lexical.RegularExpressionFirstChar ∧
      glData.alts cxHtmlTrue .lexical .RegularExpressionFirstChar = srcsOf .lexical Gen.Lexical.RegularExpressionFirstChar ∧
      glData.alts cxHtmlFalse .lexical .RegularExpressionBackslashSequence = srcsOf .lexical Gen.Lexical.RegularExpressionBackslashSequence ∧
      glData.alts cxHtmlTrue .lexical .RegularExpressionBackslashSequence = srcsOf .lexical Gen.Lexical.RegularExpressionBackslashSequence ∧
      glData.alts cxHtmlFalse .lexical .RegularExpressionClass = srcsOf .lexical Gen.Lexical.RegularExpressionClass ∧
      glData.alts cxHtmlTrue .lexical .RegularExpressionClass = srcsOf .lexical Gen.Lexical.RegularExpressionClass ∧
      glData.alts cxHtmlFalse .lexical .RegularExpressionNonTerminator = srcsOf .lexical Gen.Lexical.RegularExpressionNonTerminator ∧
      glData.alts cxHtmlTrue .lexical .RegularExpressionNonTerminator = srcsOf .lexical Gen.Lexical.RegularExpressionNonTerminator := by
    decide
  cases hd with
  | node sb hsb _ _ _ hswB =>
    have hsb := lex_mem_alts hok hsb
    rw [alts_fixed_eq haltsBody.1 haltsBody.2.1] at hsb
    simp only [srcsOf, writtenAlts, Gen.Lexical.RegularExpressionBody, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_singleton] at hsb
    subst hsb
    cases hswB with
    | leaf _ hl _ _ _ => exact nomatch hl
    | nt _ hdF _ _ _ =>
      cases hdF with
      | node sf hsf _ _ _ hswF =>
        have hsf := lex_mem_alts hok hsf
        rw [alts_fixed_eq haltsBody.2.2.1 haltsBody.2.2.2.1] at hsf
        simp only [srcsOf, writtenAlts, Gen.Lexical.RegularExpressionFirstChar, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsf
        rcases hsf with rfl | rfl | rfl
        · cases hswF with
          | butNotLeaf _ hl _ _ _ => exact nomatch hl
          | butNotN _ hdNT _ hne _ =>
            cases hdNT with
            | node snt hsnt _ _ _ hswNT =>
              have hsnt := lex_mem_alts hok hsnt
              rw [alts_fixed_eq haltsBody.2.2.2.2.2.2.2.2.1 haltsBody.2.2.2.2.2.2.2.2.2] at hsnt
              simp only [srcsOf, writtenAlts, Gen.Lexical.RegularExpressionNonTerminator, List.zipIdx_cons,
                List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_singleton] at hsnt
              subst hsnt
              cases hswNT with
              | butNotLeaf _ hl _ _ _ => exact nomatch hl
              | butNotN _ hdSC _ _ hnilNT =>
                cases hnilNT
                cases hdSC with
                | node ssc hssc _ _ _ hswSC =>
                  have hssc := lex_mem_alts hok hssc
                  rw [alts_fixed_eq alts_cert_trivia.1 alts_cert_trivia.2.1] at hssc
                  simp only [srcsOf, writtenAlts, Gen.Lexical.SourceCharacter, List.zipIdx_cons,
                    List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_singleton] at hssc
                  subst hssc
                  cases hswSC with
                  | phrase hph hnilSC =>
                    cases hnilSC
                    obtain ⟨_, hcGet, _, rfl⟩ := hph
                    have hltSz : k < cs.size := (Array.getElem?_eq_some_iff.mp hcGet).1
                    have hk1Len : k + 1 ≤ cs.toList.length := by rw [Array.length_toList]; omega
                    apply hne
                    dsimp only [AlphaSpec.ExclHolds, AlphaSpec.SymHolds, lexSpec, codeAlphaSpec]
                    rcases hc with h2f | h2a
                    · obtain ⟨hk1Sz, hex⟩ := extract_one_at h2f
                      exact ⟨.t (.text "/" false), by simp, termEnd_text_mk "/" false k (by decide) hk1Sz hex⟩
                    · obtain ⟨hk1Sz, hex⟩ := extract_one_at h2a
                      exact ⟨.t (.text "*" false), by simp, termEnd_text_mk "*" false k (by decide) hk1Sz hex⟩
        · cases hswF with
          | leaf _ hl _ _ _ => exact nomatch hl
          | nt _ hdBS _ _ _ =>
            cases hdBS with
            | node sbs hsbs _ _ _ hswBS =>
              have hsbs := lex_mem_alts hok hsbs
              rw [alts_fixed_eq haltsBody.2.2.2.2.1 haltsBody.2.2.2.2.2.1] at hsbs
              simp only [srcsOf, writtenAlts, Gen.Lexical.RegularExpressionBackslashSequence, List.zipIdx_cons,
                List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_singleton] at hsbs
              subst hsbs
              cases hswBS with
              | term ht _ =>
                obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x5C) (csRest := []) rfl ht
                rcases hc with h1 | h1 <;> (rw [h1] at hg0; cases hg0)
        · cases hswF with
          | leaf _ hl _ _ _ => exact nomatch hl
          | nt _ hdCL _ _ _ =>
            cases hdCL with
            | node scl hscl _ _ _ hswCL =>
              have hscl := lex_mem_alts hok hscl
              rw [alts_fixed_eq haltsBody.2.2.2.2.2.2.1 haltsBody.2.2.2.2.2.2.2.1] at hscl
              simp only [srcsOf, writtenAlts, Gen.Lexical.RegularExpressionClass, List.zipIdx_cons,
                List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_singleton] at hscl
              subst hscl
              cases hswCL with
              | term ht _ =>
                obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x5B) (csRest := []) rfl ht
                rcases hc with h1 | h1 <;> (rw [h1] at hg0; cases hg0)

private theorem tokLead_props (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat} :
    ∀ (sz : Nat) {n : NT} {ps : List Param} {k h : Nat} {dt : DTree},
      sizeOf dt ≤ sz →
      n ∈ tokLeadNTs →
      k ≤ cs.size →
      (lexSpec cs cx).PlainDerives n ps k h dt →
      k < h ∧
      (∃ c, cs[k]? = some c ∧ Lex.isWS Engine.builder c = false ∧ Lex.isLT c = false) ∧
      ((n == .IdentifierName || n == .IdentifierStart || n == .IdentifierStartChar || n == .UnicodeIDStart) = true →
        ∃ c, cs[k]? = some c ∧ (Engine.builder.idStart c = true ∨ c = 0x24 ∨ c = 0x5F ∨ c = 0x5C)) ∧
      ((n != .DivPunctuator && n != .RegularExpressionLiteral) = true → cs[k]? ≠ some 0x2F) ∧
      ((n != .Punctuator && n != .OtherPunctuator) = true → cs[k]? ≠ some 0x3C ∧ cs[k]? ≠ some 0x2D) ∧
      (cs[k]? = some 0x2F → (cs[k + 1]? = some 0x2F ∨ cs[k + 1]? = some 0x2A) → h = k + 1) ∧
      (cs[k]? = some 0x23 → cs[k + 1]? = some 0x21 → False) ∧
      (cs[k]? = some 0x3C → cs[k + 1]? = some 0x21 → h = k + 1) ∧
      (cs[k]? = some 0x2D → cs[k + 1]? = some 0x2D → cs[k + 2]? = some 0x3E → h ≤ k + 2) := by
  have hno21 : Engine.builder.idStart 0x21 = false := nonIdStart_of_mem (List.mem_append_right _ (by decide))
  have hno23 : Engine.builder.idStart 0x23 = false := nonIdStart_of_mem (List.mem_append_right _ (by decide))
  have hno2d : Engine.builder.idStart 0x2D = false := nonIdStart_of_mem (List.mem_append_right _ (by decide))
  have hno2f : Engine.builder.idStart 0x2F = false := nonIdStart_of_mem (List.mem_append_right _ (by decide))
  have hno3c : Engine.builder.idStart 0x3C = false := nonIdStart_of_mem (List.mem_append_right _ (by decide))
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    intro n ps k h dt hsz hnMem hkSz hd
    obtain ⟨haltsF, haltsT⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp tokLeadCert_true n hnMem)
    cases hd with
    | node s hsMem _ _ _ hsw =>
      have hsOk : tokLeadAltOk n s = true := by
        have hsM := lex_mem_alts hok hsMem
        rw [alts_lexical_eq] at hsM
        cases hhtml : Lex.html cx with
        | false =>
          simp only [hhtml, Bool.false_eq_true, ↓reduceIte] at hsM
          exact List.all_eq_true.mp haltsF s hsM
        | true =>
          simp only [hhtml, ↓reduceIte] at hsM
          exact List.all_eq_true.mp haltsT s hsM
      unfold tokLeadAltOk at hsOk
      generalize hrhs : s.alt.rhs = rhs0 at hsOk hsw
      cases rhs0 with
      | nil => cases hsOk
      | cons it0 rest =>
        cases it0 with
        | sym sym0 opt0 =>
          cases opt0 with
          | true =>
            cases sym0 with
            | t tx => cases tx <;> cases hsOk
            | nt _ _ => cases hsOk
          | false =>
            cases sym0 with
            | t tx =>
              cases tx with
              | cp _ => cases hsOk
              | text str altB =>
                dsimp only at hsOk
                cases hw : str.toList.map Char.toNat with
                | nil => rw [hw] at hsOk; cases hsOk
                | cons c0 csRest =>
                  rw [hw] at hsOk
                  dsimp only at hsOk
                  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, Bool.not_eq_true'] at hsOk
                  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hc80, hc20⟩, hc9⟩, hcb⟩, hcc⟩, hclt⟩, hidC⟩, hno2fC⟩, hno3c2d⟩, hspec⟩ := hsOk
                  cases hsw with
                  | term ht hswR =>
                    obtain ⟨hmidEq, hget0, hget1⟩ := termEnd_text_cons hw ht
                    have ⟨hmidLeH, _⟩ := lexSeqWith_le hok (codeTerm_bound Engine.builder cs _ k _ ht).2 hswR
                    refine ⟨by omega, ⟨c0, hget0, ascii_not_ws hc80 hc20 hc9 hcb hcc, hclt⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · intro hidFam
                      rw [hidFam] at hidC
                      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hidC
                      rcases hidC with (rfl | rfl) | rfl
                      · exact ⟨_, hget0, Or.inr (Or.inl rfl)⟩
                      · exact ⟨_, hget0, Or.inr (Or.inr (Or.inl rfl))⟩
                      · exact ⟨_, hget0, Or.inr (Or.inr (Or.inr rfl))⟩
                    · intro hnNotDiv hk2f
                      rw [hnNotDiv] at hno2fC
                      simp only [Bool.not_true, Bool.false_or, bne_iff_ne] at hno2fC
                      exact hno2fC (Option.some.inj (hget0.symm.trans hk2f))
                    · intro hnNotPunc
                      rw [hnNotPunc] at hno3c2d
                      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, bne_iff_ne] at hno3c2d
                      exact ⟨fun hk => hno3c2d.1 (Option.some.inj (hget0.symm.trans hk)),
                             fun hk => hno3c2d.2 (Option.some.inj (hget0.symm.trans hk))⟩
                    · intro hk2f hk1
                      have hc0Eq : c0 = 0x2F := Option.some.inj (hget0.symm.trans hk2f)
                      subst hc0Eq
                      simp only [beq_iff_eq, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, isEmpty_eq_true_iff] at hspec
                      rcases hspec with ⟨⟨rfl, rfl⟩, hcsR⟩ | ⟨⟨rfl, rfl⟩, hrestRE⟩
                      · cases hswR
                        rcases hcsR with rfl | rfl
                        · omega
                        · have h1 := hget1 0x3D [] rfl
                          rcases hk1 with h2 | h2 <;> (rw [h1] at h2; cases h2)
                      · exfalso
                        cases rest with
                        | nil => cases hrestRE
                        | cons it1 rest1 =>
                          cases it1 with
                          | sym sym1 o1 =>
                            cases o1 with
                            | true => simp at hrestRE
                            | false =>
                              cases sym1 with
                              | t _ => cases hrestRE
                              | nt m1 args1 =>
                                by_cases hm1 : m1 = .RegularExpressionBody ∧ args1 = []
                                · rcases hm1 with ⟨rfl, rfl⟩
                                  cases hswR with
                                  | leaf _ hl _ _ _ => exact nomatch hl
                                  | nt _ hdBody _ _ _ =>
                                    simp only [List.length_nil, Nat.add_zero] at hmidEq
                                    subst hmidEq
                                    exact reBody_not_slash_or_star hok hk1 hdBody
                                · cases m1 <;> cases args1 <;> first | exact absurd ⟨rfl, rfl⟩ hm1 | cases hrestRE
                          | _ => cases hrestRE
                    · intro hk23 hk21
                      have hc0Eq : c0 = 0x23 := Option.some.inj (hget0.symm.trans hk23)
                      subst hc0Eq
                      simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hspec
                      obtain ⟨⟨rfl, rfl⟩, hrestId⟩ := hspec
                      have hrestEq : rest = [.sym (.nt .IdentifierName []) false] := by
                        cases rest with
                        | nil => cases hrestId
                        | cons it1 r1 =>
                          cases r1 with
                          | cons _ _ =>
                            cases it1 with
                            | sym sym1 o1 =>
                              cases o1 with
                              | true => simp at hrestId
                              | false =>
                                cases sym1 with
                                | t _ => cases hrestId
                                | nt m1 args1 => cases m1 <;> cases args1 <;> cases hrestId
                            | _ => cases hrestId
                          | nil =>
                            cases it1 with
                            | sym sym1 o1 =>
                              cases o1 with
                              | true => simp at hrestId
                              | false =>
                                cases sym1 with
                                | t _ => cases hrestId
                                | nt m1 args1 =>
                                  cases m1 <;> cases args1 <;> first | rfl | cases hrestId
                            | _ => cases hrestId
                      subst hrestEq
                      cases hswR with
                      | leaf _ hl _ _ _ => exact nomatch hl
                      | nt _ hdId _ _ _ =>
                        have hidMem : NT.IdentifierName ∈ tokLeadNTs := by decide
                        simp only [List.length_nil, Nat.add_zero] at hmidEq
                        subst hmidEq
                        have ⟨_, _, hidFam, _⟩ := ih (sz - 1)
                          (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega)
                          (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega)
                          hidMem (by have := (Array.getElem?_eq_some_iff.mp hk23).1; omega) hdId
                        obtain ⟨c1, hc1Get, hc1Ok⟩ := hidFam rfl
                        have hc1Eq : c1 = 0x21 := Option.some.inj (hc1Get.symm.trans hk21)
                        subst hc1Eq
                        rcases hc1Ok with h1 | h1 | h1 | h1
                        · rw [hno21] at h1; cases h1
                        · omega
                        · omega
                        · omega
                    · intro hk3c hk21
                      have hc0Eq : c0 = 0x3C := Option.some.inj (hget0.symm.trans hk3c)
                      subst hc0Eq
                      simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, isEmpty_eq_true_iff] at hspec
                      obtain ⟨rfl, hcsR⟩ := hspec
                      cases hswR
                      rcases hcsR with ((rfl | rfl) | rfl) | rfl
                      · omega
                      · have h1 := hget1 0x3D [] rfl; rw [h1] at hk21; cases hk21
                      · have h1 := hget1 0x3C [] rfl; rw [h1] at hk21; cases hk21
                      · have h1 := hget1 0x3C [0x3D] rfl; rw [h1] at hk21; cases hk21
                    · intro hk2d _ _
                      have hc0Eq : c0 = 0x2D := Option.some.inj (hget0.symm.trans hk2d)
                      subst hc0Eq
                      simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, isEmpty_eq_true_iff] at hspec
                      obtain ⟨rfl, hcsR⟩ := hspec
                      cases hswR
                      rcases hcsR with (rfl | rfl) | rfl <;> simp at hmidEq <;> omega
            | nt m args =>
              dsimp only at hsOk
              simp only [Bool.and_eq_true, List.contains_iff_mem] at hsOk
              obtain ⟨⟨⟨⟨⟨⟨⟨⟨hmMem, hnNotDiv⟩, hnNotRE⟩, hnNotOther⟩, hmNotDiv⟩, hmNotRE⟩, hmNotPriv⟩, hmNotPunc⟩, hmFam⟩ := hsOk
              cases hsw with
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hd0 _ _ hswR =>
                have ⟨hkm, hwsLt, hid0, hno2f0, hno3c2d0, _, hhash0, hlt0, hdash0⟩ := ih (sz - 1)
                  (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega)
                  (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega)
                  hmMem hkSz hd0
                have ⟨hmidLeH, _⟩ := lexSeqWith_le hok (lexPlain_to_derives hok hkSz hd0).2.1 hswR
                have hno2fM : cs[k]? ≠ some 0x2F := hno2f0 (Bool.and_eq_true_iff.mpr ⟨hmNotDiv, hmNotRE⟩)
                refine ⟨by omega, hwsLt, ?_, (fun _ => hno2fM), ?_, (fun hk _ => absurd hk hno2fM), hhash0, ?_, ?_⟩
                · intro hidN
                  have hnp : (n == .Punctuator) = false := by
                    simp only [Bool.or_eq_true, beq_iff_eq] at hidN
                    rcases hidN with ((rfl | rfl) | rfl) | rfl <;> rfl
                  simp only [hnp, Bool.false_eq_true, ↓reduceIte, hidN] at hmFam
                  exact hid0 hmFam
                · intro hnNotPO
                  simp only [Bool.and_eq_true] at hnNotPO
                  have hnp : (n == .Punctuator) = false := by
                    rw [Bool.eq_false_iff, ne_eq]; exact bne_iff_ne.mp hnNotPO.1
                  simp only [hnp, Bool.false_eq_true, ↓reduceIte] at hmFam
                  by_cases hidN : (n == .IdentifierName || n == .IdentifierStart || n == .IdentifierStartChar || n == .UnicodeIDStart) = true
                  · simp only [hidN, ↓reduceIte] at hmFam
                    obtain ⟨c, hcGet, hcOk⟩ := hid0 hmFam
                    refine ⟨fun hk => ?_, fun hk => ?_⟩
                    · have := Option.some.inj (hcGet.symm.trans hk); subst this
                      rcases hcOk with h1 | h1 | h1 | h1
                      · rw [hno3c] at h1; cases h1
                      · omega
                      · omega
                      · omega
                    · have := Option.some.inj (hcGet.symm.trans hk); subst this
                      rcases hcOk with h1 | h1 | h1 | h1
                      · rw [hno2d] at h1; cases h1
                      · omega
                      · omega
                      · omega
                  · simp only [hidN, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hmFam
                    exact hno3c2d0 (Bool.and_eq_true_iff.mpr ⟨hmNotPunc, hmFam.1.1.1.1.1⟩)
                · intro hk3c hk21
                  by_cases hnp : (n == .Punctuator) = true
                  · simp only [hnp, ↓reduceIte, Bool.and_eq_true, isEmpty_eq_true_iff] at hmFam
                    rcases hmFam with ⟨rfl, _⟩
                    cases hswR
                    exact hlt0 hk3c hk21
                  · have hnpF : (n == .Punctuator) = false := Bool.eq_false_iff.mpr hnp
                    simp only [hnpF, Bool.false_eq_true, ↓reduceIte] at hmFam
                    by_cases hidN : (n == .IdentifierName || n == .IdentifierStart || n == .IdentifierStartChar || n == .UnicodeIDStart) = true
                    · simp only [hidN, ↓reduceIte] at hmFam
                      obtain ⟨c, hcGet, hcOk⟩ := hid0 hmFam
                      have := Option.some.inj (hcGet.symm.trans hk3c); subst this
                      rcases hcOk with h1 | h1 | h1 | h1
                      · rw [hno3c] at h1; cases h1
                      · omega
                      · omega
                      · omega
                    · simp only [hidN, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hmFam
                      exact absurd hk3c (hno3c2d0 (Bool.and_eq_true_iff.mpr ⟨hmNotPunc, hmFam.1.1.1.1.1⟩)).1
                · intro hk2d hk2d1 hk3e
                  by_cases hnp : (n == .Punctuator) = true
                  · simp only [hnp, ↓reduceIte, Bool.and_eq_true, isEmpty_eq_true_iff] at hmFam
                    rcases hmFam with ⟨rfl, _⟩
                    cases hswR
                    exact hdash0 hk2d hk2d1 hk3e
                  · have hnpF : (n == .Punctuator) = false := Bool.eq_false_iff.mpr hnp
                    simp only [hnpF, Bool.false_eq_true, ↓reduceIte] at hmFam
                    by_cases hidN : (n == .IdentifierName || n == .IdentifierStart || n == .IdentifierStartChar || n == .UnicodeIDStart) = true
                    · simp only [hidN, ↓reduceIte] at hmFam
                      obtain ⟨c, hcGet, hcOk⟩ := hid0 hmFam
                      have := Option.some.inj (hcGet.symm.trans hk2d); subst this
                      rcases hcOk with h1 | h1 | h1 | h1
                      · rw [hno2d] at h1; cases h1
                      · omega
                      · omega
                      · omega
                    · simp only [hidN, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hmFam
                      exact absurd hk2d (hno3c2d0 (Bool.and_eq_true_iff.mpr ⟨hmNotPunc, hmFam.1.1.1.1.1⟩)).2
        | phrase ph =>
          cases rest with
          | cons _ _ => cases ph <;> cases hsOk
          | nil =>
            cases ph with
            | idStart =>
              rw [beq_iff_eq] at hsOk
              subst hsOk
              cases hsw with
              | phrase hph hnil =>
                cases hnil
                obtain ⟨c, hcGet, hpok, rfl⟩ := hph
                have hidc : Engine.builder.idStart c = true := hpok
                have hnws : Lex.isWS Engine.builder c = false := by
                  cases hw : Lex.isWS Engine.builder c with
                  | false => rfl
                  | true => rw [isWS_not_idStart hw] at hidc; cases hidc
                have hnlt : Lex.isLT c = false := by
                  cases hl : Lex.isLT c with
                  | false => rfl
                  | true => rw [isLT_not_idStart hl] at hidc; cases hidc
                have hneC : ∀ v, Engine.builder.idStart v = false → cs[k]? ≠ some v := by
                  intro v hv hk
                  have := Option.some.inj (hcGet.symm.trans hk); subst this
                  rw [hv] at hidc; cases hidc
                refine ⟨by omega, ⟨c, hcGet, hnws, hnlt⟩,
                  (fun _ => ⟨c, hcGet, Or.inl hidc⟩),
                  (fun _ => hneC 0x2F hno2f),
                  (fun _ => ⟨hneC 0x3C hno3c, hneC 0x2D hno2d⟩),
                  (fun hk _ => absurd hk (hneC 0x2F hno2f)),
                  (fun hk _ => hneC 0x23 hno23 hk),
                  (fun hk _ => absurd hk (hneC 0x3C hno3c)),
                  (fun hk _ _ => absurd hk (hneC 0x2D hno2d))⟩
            | _ => cases hsOk
        | butNot _ _ | lookahead _ | noLT | empty | onlyIf _ => cases hsOk

/-! ## Exact span characterizations of non-token lexical nonterminals -/

private theorem extract_one_eq {cs : Array Nat} {i c : Nat} (h : cs[i]? = some c) :
    i + 1 ≤ cs.size ∧ (cs.extract i (i + 1)).toList = [c] := by
  have hlt : i < cs.size := (Array.getElem?_eq_some_iff.mp h).1
  have hi1Len : i + 1 ≤ cs.toList.length := by rw [Array.length_toList]; omega
  refine ⟨by omega, ?_⟩
  rw [extract_toList_eq_slice]
  have hgL : cs.toList[i]? = some c := by simpa using h
  obtain ⟨hil, hiv⟩ := List.getElem?_eq_some_iff.mp hgL
  exact (slice_singleton_iff (by omega) hi1Len).mpr
    ⟨rfl, hgL, by rw [List.drop_eq_getElem_cons hil, hiv]⟩

private theorem extract_two_eq {cs : Array Nat} {i c0 c1 : Nat}
    (h0 : cs[i]? = some c0) (h1 : cs[i + 1]? = some c1) :
    i + 2 ≤ cs.size ∧ (cs.extract i (i + 2)).toList = [c0, c1] := by
  have hlt1 : i + 1 < cs.size := (Array.getElem?_eq_some_iff.mp h1).1
  refine ⟨by omega, ?_⟩
  rw [extract_toList_eq_slice]
  unfold slice
  have hl0 : i < cs.toList.length := by rw [Array.length_toList]; omega
  have hl1 : i + 1 < cs.toList.length := by rw [Array.length_toList]; omega
  have hv0 : cs.toList[i] = c0 := Option.some.inj ((List.getElem?_eq_getElem hl0).symm.trans (by simpa using h0))
  have hv1 : cs.toList[i + 1] = c1 := Option.some.inj ((List.getElem?_eq_getElem hl1).symm.trans (by simpa using h1))
  rw [show i + 2 - i = 2 from by omega, List.drop_eq_getElem_cons hl0, hv0, List.take_succ_cons,
    List.drop_eq_getElem_cons hl1, hv1, List.take_succ_cons, List.take_zero]

private theorem extract_three_eq {cs : Array Nat} {i c0 c1 c2 : Nat}
    (h0 : cs[i]? = some c0) (h1 : cs[i + 1]? = some c1) (h2 : cs[i + 2]? = some c2) :
    i + 3 ≤ cs.size ∧ (cs.extract i (i + 3)).toList = [c0, c1, c2] := by
  have hlt2 : i + 2 < cs.size := (Array.getElem?_eq_some_iff.mp h2).1
  refine ⟨by omega, ?_⟩
  rw [extract_toList_eq_slice]
  unfold slice
  have hl0 : i < cs.toList.length := by rw [Array.length_toList]; omega
  have hl1 : i + 1 < cs.toList.length := by rw [Array.length_toList]; omega
  have hl2 : i + 2 < cs.toList.length := by rw [Array.length_toList]; omega
  have hv0 : cs.toList[i] = c0 := Option.some.inj ((List.getElem?_eq_getElem hl0).symm.trans (by simpa using h0))
  have hv1 : cs.toList[i + 1] = c1 := Option.some.inj ((List.getElem?_eq_getElem hl1).symm.trans (by simpa using h1))
  have hv2 : cs.toList[i + 2] = c2 := Option.some.inj ((List.getElem?_eq_getElem hl2).symm.trans (by simpa using h2))
  rw [show i + 3 - i = 3 from by omega, List.drop_eq_getElem_cons hl0, hv0, List.take_succ_cons,
    List.drop_eq_getElem_cons hl1, hv1, List.take_succ_cons,
    List.drop_eq_getElem_cons hl2, hv2, List.take_succ_cons, List.take_zero]

private theorem extract_four_eq {cs : Array Nat} {i c0 c1 c2 c3 : Nat}
    (h0 : cs[i]? = some c0) (h1 : cs[i + 1]? = some c1)
    (h2 : cs[i + 2]? = some c2) (h3 : cs[i + 3]? = some c3) :
    i + 4 ≤ cs.size ∧ (cs.extract i (i + 4)).toList = [c0, c1, c2, c3] := by
  have hlt3 : i + 3 < cs.size := (Array.getElem?_eq_some_iff.mp h3).1
  refine ⟨by omega, ?_⟩
  rw [extract_toList_eq_slice]
  unfold slice
  have hl0 : i < cs.toList.length := by rw [Array.length_toList]; omega
  have hl1 : i + 1 < cs.toList.length := by rw [Array.length_toList]; omega
  have hl2 : i + 2 < cs.toList.length := by rw [Array.length_toList]; omega
  have hl3 : i + 3 < cs.toList.length := by rw [Array.length_toList]; omega
  have hv0 : cs.toList[i] = c0 := Option.some.inj ((List.getElem?_eq_getElem hl0).symm.trans (by simpa using h0))
  have hv1 : cs.toList[i + 1] = c1 := Option.some.inj ((List.getElem?_eq_getElem hl1).symm.trans (by simpa using h1))
  have hv2 : cs.toList[i + 2] = c2 := Option.some.inj ((List.getElem?_eq_getElem hl2).symm.trans (by simpa using h2))
  have hv3 : cs.toList[i + 3] = c3 := Option.some.inj ((List.getElem?_eq_getElem hl3).symm.trans (by simpa using h3))
  rw [show i + 4 - i = 4 from by omega, List.drop_eq_getElem_cons hl0, hv0, List.take_succ_cons,
    List.drop_eq_getElem_cons hl1, hv1, List.take_succ_cons,
    List.drop_eq_getElem_cons hl2, hv2, List.take_succ_cons,
    List.drop_eq_getElem_cons hl3, hv3, List.take_succ_cons, List.take_zero]

theorem sourceCharacter_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .SourceCharacter [] i j dt) ↔
      ∃ c, cs[i]? = some c ∧ j = i + 1 := by
  have halts := alts_fixed_eq (cx := cx) alts_cert_trivia.1 alts_cert_trivia.2.1
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp [srcsOf, writtenAlts, Gen.Lexical.SourceCharacter] at hs
    subst hs
    cases hsw with
    | phrase hph hnil =>
      cases hnil
      obtain ⟨c, hc, _, rfl⟩ := hph
      exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hcle : c ≤ 0x10FFFF := hcp c (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hc))
    have hpok : Code.phraseOk Engine.builder .anyCodePoint c = true := by
      simp [Code.phraseOk, hcle]
    let s0 : Src := ⟨.lexical, Gen.Lexical.SourceCharacter, 0, ⟨[], [.phrase .anyCodePoint], none⟩⟩
    have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .SourceCharacter := by rw [halts]; exact mem_of_get? 0 rfl
    obtain ⟨id, hd⟩ := mkLexPlainSimple hok hs0 rfl (.phrase ⟨c, hc, hpok, rfl⟩ .nil)
    exact ⟨_, hd⟩

theorem whiteSpace_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat} {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .WhiteSpace [] i j dt) ↔
      ∃ c, cs[i]? = some c ∧ Lex.isWS Engine.builder c = true ∧ j = i + 1 := by
  have halts := alts_fixed_eq (cx := cx) alts_cert_trivia.2.2.1 alts_cert_trivia.2.2.2.1
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp only [srcsOf, writtenAlts, Gen.Lexical.WhiteSpace, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> (
      cases hsw with
      | term ht hnil =>
        cases hnil
        replace ht := lexTerm_eq ht; unfold Code.termEnd at ht
        rcases opt_none_or_some cs[i]? with hn | ⟨c, hc⟩
        · rw [hn] at ht; cases ht
        · rw [hc] at ht
          dsimp only [Bind.bind, Option.bind, CodePointName.codePoint] at ht
          split at ht
          · next hm => injection ht with hj; exact ⟨c, hc, by simp [Lex.isWS, hm], hj.symm⟩
          · cases ht)
  · rintro ⟨c, hc, hws, rfl⟩
    unfold Lex.isWS at hws
    simp only [Bool.or_eq_true, beq_iff_eq] at hws
    rcases hws with (((rfl | rfl) | rfl) | rfl) | husp
    · let s0 : Src := ⟨.lexical, Gen.Lexical.WhiteSpace, 0, ⟨[], [.sym (.t (.cp .TAB)) false], none⟩⟩
      have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .WhiteSpace := by rw [halts]; exact mem_of_get? 0 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .TAB) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht .nil); exact ⟨_, hd⟩
    · let s0 : Src := ⟨.lexical, Gen.Lexical.WhiteSpace, 1, ⟨[], [.sym (.t (.cp .VT)) false], none⟩⟩
      have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .WhiteSpace := by rw [halts]; exact mem_of_get? 1 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .VT) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht .nil); exact ⟨_, hd⟩
    · let s0 : Src := ⟨.lexical, Gen.Lexical.WhiteSpace, 2, ⟨[], [.sym (.t (.cp .FF)) false], none⟩⟩
      have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .WhiteSpace := by rw [halts]; exact mem_of_get? 2 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .FF) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht .nil); exact ⟨_, hd⟩
    · let s0 : Src := ⟨.lexical, Gen.Lexical.WhiteSpace, 3, ⟨[], [.sym (.t (.cp .ZWNBSP)) false], none⟩⟩
      have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .WhiteSpace := by rw [halts]; exact mem_of_get? 3 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .ZWNBSP) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht .nil); exact ⟨_, hd⟩
    · let s0 : Src := ⟨.lexical, Gen.Lexical.WhiteSpace, 4, ⟨[], [.sym (.t (.cp .USP)) false], none⟩⟩
      have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .WhiteSpace := by rw [halts]; exact mem_of_get? 4 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .USP) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint, husp]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht .nil); exact ⟨_, hd⟩

theorem lineTerminator_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat} {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .LineTerminator [] i j dt) ↔
      ∃ c, cs[i]? = some c ∧ Lex.isLT c = true ∧ j = i + 1 := by
  have halts := alts_fixed_eq (cx := cx) alts_cert_trivia.2.2.2.2.1 alts_cert_trivia.2.2.2.2.2.1
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp only [srcsOf, writtenAlts, Gen.Lexical.LineTerminator, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> (
      cases hsw with
      | term ht hnil =>
        cases hnil
        replace ht := lexTerm_eq ht; unfold Code.termEnd at ht
        rcases opt_none_or_some cs[i]? with hn | ⟨c, hc⟩
        · rw [hn] at ht; cases ht
        · rw [hc] at ht
          dsimp only [Bind.bind, Option.bind, CodePointName.codePoint] at ht
          split at ht
          · next hm => injection ht with hj; exact ⟨c, hc, by simp [Lex.isLT, beq_iff_eq.mp hm], hj.symm⟩
          · cases ht)
  · rintro ⟨c, hc, hlt, rfl⟩
    unfold Lex.isLT at hlt
    simp only [Bool.or_eq_true, beq_iff_eq] at hlt
    rcases hlt with ((rfl | rfl) | rfl) | rfl
    · let s0 : Src := ⟨.lexical, Gen.Lexical.LineTerminator, 0, ⟨[], [.sym (.t (.cp .LF)) false], none⟩⟩
      have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .LineTerminator := by rw [halts]; exact mem_of_get? 0 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .LF) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht .nil); exact ⟨_, hd⟩
    · let s0 : Src := ⟨.lexical, Gen.Lexical.LineTerminator, 1, ⟨[], [.sym (.t (.cp .CR)) false], none⟩⟩
      have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .LineTerminator := by rw [halts]; exact mem_of_get? 1 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .CR) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht .nil); exact ⟨_, hd⟩
    · let s0 : Src := ⟨.lexical, Gen.Lexical.LineTerminator, 2, ⟨[], [.sym (.t (.cp .LS)) false], none⟩⟩
      have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .LineTerminator := by rw [halts]; exact mem_of_get? 2 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .LS) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht .nil); exact ⟨_, hd⟩
    · let s0 : Src := ⟨.lexical, Gen.Lexical.LineTerminator, 3, ⟨[], [.sym (.t (.cp .PS)) false], none⟩⟩
      have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .LineTerminator := by rw [halts]; exact mem_of_get? 3 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .PS) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht .nil); exact ⟨_, hd⟩

private theorem dec_lineTerminator_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {i j : Nat} (hj : j ≤ cs.size) :
    Code.dec Engine.builder cs .lexical cx 16 .LineTerminator [] i j = true ↔
      ∃ c, cs[i]? = some c ∧ Lex.isLT c = true ∧ j = i + 1 := by
  have halts := alts_fixed_eq (cx := cx) alts_cert_trivia.2.2.2.2.1 alts_cert_trivia.2.2.2.2.2.1
  unfold Code.dec
  rw [altsOf_eq hok, halts]
  simp only [srcsOf, writtenAlts, Gen.Lexical.LineTerminator, List.zipIdx_cons, List.zipIdx_nil,
    List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, List.all_nil, Bool.true_and,
    Code.decSeq, Bool.false_and, Bool.false_or]
  rcases opt_none_or_some cs[i]? with hn | ⟨c, hc⟩
  · simp [Code.termEnd, hn]
  · simp only [Code.termEnd, hc, Bind.bind, Option.bind, CodePointName.codePoint, Lex.isLT]
    by_cases h0 : c = 0xA
    · subst h0; simp [show i + 1 ≤ j ∧ i + 1 = j ↔ j = i + 1 from by omega]
    · by_cases h1 : c = 0xD
      · subst h1; simp [show i + 1 ≤ j ∧ i + 1 = j ↔ j = i + 1 from by omega]
      · by_cases h2 : c = 0x2028
        · subst h2; simp [show i + 1 ≤ j ∧ i + 1 = j ↔ j = i + 1 from by omega]
        · by_cases h3 : c = 0x2029
          · subst h3; simp [show i + 1 ≤ j ∧ i + 1 = j ↔ j = i + 1 from by omega]
          · have _ := hj; simp [h0, h1, h2, h3]

theorem lineTerminatorSequence_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat} {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .LineTerminatorSequence [] i j dt) ↔
      ∃ c, cs[i]? = some c ∧ Lex.isLT c = true ∧
        j = (if c == 0xD && cs[i + 1]? == some 0xA then i + 2 else i + 1) := by
  have halts := alts_fixed_eq (cx := cx) alts_cert_trivia.2.2.2.2.2.2.1 alts_cert_trivia.2.2.2.2.2.2.2.1
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp only [srcsOf, writtenAlts, Gen.Lexical.LineTerminatorSequence, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · cases hsw with | term ht hnil =>
        cases hnil; replace ht := lexTerm_eq ht; unfold Code.termEnd at ht
        rcases opt_none_or_some cs[i]? with hn | ⟨c, hc⟩
        · rw [hn] at ht; cases ht
        · rw [hc] at ht; dsimp only [Bind.bind, Option.bind, CodePointName.codePoint] at ht
          split at ht
          · next hm => injection ht with hj; have := beq_iff_eq.mp hm; subst this; exact ⟨0xA, hc, rfl, hj.symm⟩
          · cases ht
    · cases hsw with | term ht hr => cases hr with | look hlk hnil =>
        cases hnil; replace ht := lexTerm_eq ht; unfold Code.termEnd at ht
        rcases opt_none_or_some cs[i]? with hn | ⟨c, hc⟩
        · rw [hn] at ht; cases ht
        · rw [hc] at ht; dsimp only [Bind.bind, Option.bind, CodePointName.codePoint] at ht
          split at ht
          · next hm =>
            injection ht with hj; subst hj
            have hcEq := beq_iff_eq.mp hm; subst hcEq
            dsimp only [AlphaSpec.LookHolds, lexSpec, codeAlphaSpec] at hlk
            have hnotLF : (cs[i + 1]? == some 0xA) = false := by
              rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]
              intro hlf
              apply hlk
              simp [Code.startsWith, Code.termEnd, hlf, CodePointName.codePoint]
            exact ⟨0xD, hc, rfl, by simp [hnotLF]⟩
          · cases ht
    · cases hsw with | term ht hnil =>
        cases hnil; replace ht := lexTerm_eq ht; unfold Code.termEnd at ht
        rcases opt_none_or_some cs[i]? with hn | ⟨c, hc⟩
        · rw [hn] at ht; cases ht
        · rw [hc] at ht; dsimp only [Bind.bind, Option.bind, CodePointName.codePoint] at ht
          split at ht
          · next hm => injection ht with hj; have := beq_iff_eq.mp hm; subst this; exact ⟨0x2028, hc, rfl, hj.symm⟩
          · cases ht
    · cases hsw with | term ht hnil =>
        cases hnil; replace ht := lexTerm_eq ht; unfold Code.termEnd at ht
        rcases opt_none_or_some cs[i]? with hn | ⟨c, hc⟩
        · rw [hn] at ht; cases ht
        · rw [hc] at ht; dsimp only [Bind.bind, Option.bind, CodePointName.codePoint] at ht
          split at ht
          · next hm => injection ht with hj; have := beq_iff_eq.mp hm; subst this; exact ⟨0x2029, hc, rfl, hj.symm⟩
          · cases ht
    · cases hsw with | term ht1 hr => cases hr with | term ht2 hnil =>
        cases hnil; replace ht1 := lexTerm_eq ht1; replace ht2 := lexTerm_eq ht2; unfold Code.termEnd at ht1 ht2
        rcases opt_none_or_some cs[i]? with hn | ⟨c, hc⟩
        · rw [hn] at ht1; cases ht1
        · rw [hc] at ht1; dsimp only [Bind.bind, Option.bind, CodePointName.codePoint] at ht1
          split at ht1
          · next hm1 =>
            injection ht1 with hj1; subst hj1
            have hcEq := beq_iff_eq.mp hm1; subst hcEq
            rcases opt_none_or_some cs[i + 1]? with hn2 | ⟨c2, hc2⟩
            · rw [hn2] at ht2; cases ht2
            · rw [hc2] at ht2; dsimp only [Bind.bind, Option.bind, CodePointName.codePoint] at ht2
              split at ht2
              · next hm2 =>
                injection ht2 with hj2
                have hc2Eq := beq_iff_eq.mp hm2; subst hc2Eq
                exact ⟨0xD, hc, rfl, by simp [hc2, hj2.symm]⟩
              · cases ht2
          · cases ht1
  · rintro ⟨c, hc, hlt, rfl⟩
    unfold Lex.isLT at hlt
    simp only [Bool.or_eq_true, beq_iff_eq] at hlt
    rcases hlt with ((rfl | rfl) | rfl) | rfl
    · let s0 : Src := ⟨.lexical, Gen.Lexical.LineTerminatorSequence, 0, ⟨[], [.sym (.t (.cp .LF)) false], none⟩⟩
      have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .LineTerminatorSequence := by rw [halts]; exact mem_of_get? 0 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .LF) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht .nil); exact ⟨_, hd⟩
    · by_cases hlf : (cs[i + 1]? == some 0xA) = true
      · simp only [beq_self_eq_true, Bool.true_and, hlf, ↓reduceIte]
        rw [beq_iff_eq] at hlf
        let s4 : Src := ⟨.lexical, Gen.Lexical.LineTerminatorSequence, 4, ⟨[], [.sym (.t (.cp .CR)) false, .sym (.t (.cp .LF)) false], none⟩⟩
        have hs4 : s4 ∈ Ecma.Spec.gl.alts cx .lexical .LineTerminatorSequence := by rw [halts]; exact mem_of_get? 4 rfl
        have ht1 : Code.termEnd Engine.builder cs (.cp .CR) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
        have ht2 : Code.termEnd Engine.builder cs (.cp .LF) (i + 1) = some (i + 2) := by simp [Code.termEnd, hlf, CodePointName.codePoint]
        obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs4 rfl (.term ht1 (.term ht2 .nil)); exact ⟨_, hd⟩
      · have hlfF : (cs[i + 1]? == some 0xA) = false := Bool.eq_false_iff.mpr hlf
        simp only [beq_self_eq_true, Bool.true_and, hlfF, Bool.false_eq_true, ↓reduceIte]
        let s1 : Src := ⟨.lexical, Gen.Lexical.LineTerminatorSequence, 1, ⟨[], [.sym (.t (.cp .CR)) false, .lookahead (.ne [.t (.cp .LF)])], none⟩⟩
        have hs1 : s1 ∈ Ecma.Spec.gl.alts cx .lexical .LineTerminatorSequence := by rw [halts]; exact mem_of_get? 1 rfl
        have ht1 : Code.termEnd Engine.builder cs (.cp .CR) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
        have hlk : (lexSpec cs cx).LookHolds (.ne [.t (.cp .LF)]) (i + 1) := by
          dsimp only [AlphaSpec.LookHolds, lexSpec, codeAlphaSpec]
          intro hsw
          unfold Code.startsWith Code.termEnd at hsw
          rcases opt_none_or_some cs[i + 1]? with hn | ⟨c2, hc2⟩
          · rw [hn] at hsw; cases hsw
          · rw [hc2] at hsw; dsimp only [Bind.bind, Option.bind, CodePointName.codePoint] at hsw
            by_cases h2 : (c2 == 0xA) = true
            · exact hlf (beq_iff_eq.mpr (hc2.trans (congrArg some (beq_iff_eq.mp h2))))
            · simp [h2] at hsw
        obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs1 rfl (.term ht1 (.look hlk .nil)); exact ⟨_, hd⟩
    · let s2 : Src := ⟨.lexical, Gen.Lexical.LineTerminatorSequence, 2, ⟨[], [.sym (.t (.cp .LS)) false], none⟩⟩
      have hs2 : s2 ∈ Ecma.Spec.gl.alts cx .lexical .LineTerminatorSequence := by rw [halts]; exact mem_of_get? 2 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .LS) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs2 rfl (.term ht .nil); exact ⟨_, hd⟩
    · let s3 : Src := ⟨.lexical, Gen.Lexical.LineTerminatorSequence, 3, ⟨[], [.sym (.t (.cp .PS)) false], none⟩⟩
      have hs3 : s3 ∈ Ecma.Spec.gl.alts cx .lexical .LineTerminatorSequence := by rw [halts]; exact mem_of_get? 3 rfl
      have ht : Code.termEnd Engine.builder cs (.cp .PS) i = some (i + 1) := by simp [Code.termEnd, hc, CodePointName.codePoint]
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs3 rfl (.term ht .nil); exact ⟨_, hd⟩

theorem singleLineCommentChar_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .SingleLineCommentChar [] i j dt) ↔
      ∃ c, cs[i]? = some c ∧ Lex.isLT c = false ∧ j = i + 1 := by
  have halts := alts_fixed_eq (cx := cx)
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hltNe : (altsOf cx .lexical .LineTerminator).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.2.2.2.2.1 alts_cert_trivia.2.2.2.2.2.1) rfl
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp [srcsOf, writtenAlts, Gen.Lexical.SingleLineCommentChar] at hs
    subst hs
    cases hsw with
    | butNotLeaf _ hl _ _ _ => exact nomatch hl
    | butNotN _ hdSC _ hne hnil =>
      cases hnil
      obtain ⟨c, hc, rfl⟩ := (sourceCharacter_iff hok hcp).mp ⟨_, hdSC⟩
      have hi1 : i + 1 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hc).1; omega
      have hnlt : Lex.isLT c = false := by
        cases hlt : Lex.isLT c with
        | false => rfl
        | true =>
          exfalso; apply hne
          dsimp only [AlphaSpec.ExclHolds, AlphaSpec.SymHolds, lexSpec, codeAlphaSpec, Code.alpha]
          simp only [hltNe, Bool.not_false, ↓reduceIte]
          exact (dec_lineTerminator_iff hok hi1).mpr ⟨c, hc, hlt, rfl⟩
      exact ⟨c, hc, hnlt, rfl⟩
  · rintro ⟨c, hc, hnlt, rfl⟩
    obtain ⟨dtSC, hdSC⟩ := (sourceCharacter_iff hok hcp).mpr ⟨c, hc, rfl⟩
    have hi1 : i + 1 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hc).1; omega
    have hscNe : (altsOf cx .lexical .SourceCharacter).isEmpty = false :=
      altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.1 alts_cert_trivia.2.1) rfl
    have hne : ¬ (lexSpec cs cx).ExclHolds
        ⟨.lexical, Gen.Lexical.SingleLineCommentChar, 0, ⟨[], [.butNot (.nt .SourceCharacter []) (.sym (.nt .LineTerminator []))], none⟩⟩
        0 [] i (i + 1) (.sym (.nt .LineTerminator [])) := by
      dsimp only [AlphaSpec.ExclHolds, AlphaSpec.SymHolds, lexSpec, codeAlphaSpec, Code.alpha]
      simp only [hltNe, Bool.not_false, ↓reduceIte]
      intro hdec
      obtain ⟨c', hc', hlt', _⟩ := (dec_lineTerminator_iff hok hi1).mp hdec
      rw [hc] at hc'; injection hc' with hcc; subst hcc; rw [hnlt] at hlt'; cases hlt'
    let s0 : Src := ⟨.lexical, Gen.Lexical.SingleLineCommentChar, 0,
      ⟨[], [.butNot (.nt .SourceCharacter []) (.sym (.nt .LineTerminator []))], none⟩⟩
    have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineCommentChar := by rw [halts]; exact mem_of_get? 0 rfl
    obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.butNotN hscNe hdSC rfl hne .nil)
    exact ⟨_, hd⟩

theorem singleLineCommentChars_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) :
    ∀ {i j : Nat},
      (∃ dt, (lexSpec cs cx).PlainDerives .SingleLineCommentChars [] i j dt) ↔
        (i < j ∧ j ≤ cs.size ∧ ∀ p, i ≤ p → p < j → ∃ c, cs[p]? = some c ∧ Lex.isLT c = false) := by
  have halts := alts_fixed_eq (cx := cx)
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcharNe : (altsOf cx .lexical .SingleLineCommentChar).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
  let s0 : Src := ⟨.lexical, Gen.Lexical.SingleLineCommentChars, 0,
    ⟨[], [.sym (.nt .SingleLineCommentChar []) false, .sym (.nt .SingleLineCommentChars []) true], none⟩⟩
  have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineCommentChars := by rw [halts]; exact mem_of_get? 0 rfl
  have hcharsNe : (altsOf cx .lexical .SingleLineCommentChars).isEmpty = false := altsOf_nonempty_of_mem hok hs0
  have hfwd : ∀ (sz : Nat) {i j : Nat} {dt : DTree}, sizeOf dt ≤ sz →
      (lexSpec cs cx).PlainDerives .SingleLineCommentChars [] i j dt →
      i < j ∧ j ≤ cs.size ∧ ∀ p, i ≤ p → p < j → ∃ c, cs[p]? = some c ∧ Lex.isLT c = false := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ih =>
      intro i j dt hsz hd
      cases hd with
      | node s hs _ _ _ hsw =>
        have hs := lex_mem_alts hok hs
        rw [halts] at hs
        simp [srcsOf, writtenAlts, Gen.Lexical.SingleLineCommentChars] at hs
        subst hs
        cases hsw with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdC _ _ hr =>
          obtain ⟨c, hc, hnlt, rfl⟩ := (singleLineCommentChar_iff hok hcp).mp ⟨_, hdC⟩
          have hi1 : i + 1 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hc).1; omega
          cases hr with
          | absent hnil =>
            cases hnil
            exact ⟨by omega, hi1, fun p hp1 hp2 => by rw [show p = i from by omega]; exact ⟨c, hc, hnlt⟩⟩
          | leaf _ hl _ _ _ => exact nomatch hl
          | nt _ hdR _ _ hnil =>
            cases hnil
            have ⟨hltR, hleR, hallR⟩ := ih (sz - 1)
              (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega)
              (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega) hdR
            refine ⟨by omega, hleR, fun p hp1 hp2 => ?_⟩
            by_cases hpi : p = i
            · subst hpi; exact ⟨c, hc, hnlt⟩
            · exact hallR p (by omega) hp2
  have hbwd : ∀ (len : Nat) {i j : Nat}, j - i = len →
      i < j → j ≤ cs.size → (∀ p, i ≤ p → p < j → ∃ c, cs[p]? = some c ∧ Lex.isLT c = false) →
      ∃ dt, (lexSpec cs cx).PlainDerives .SingleLineCommentChars [] i j dt := by
    intro len
    induction len with
    | zero => intro i j hlen hlt; omega
    | succ len ih =>
      intro i j hlen hlt hle hall
      obtain ⟨c, hc, hnlt⟩ := hall i (Nat.le_refl _) hlt
      obtain ⟨dtC, hdC⟩ := (singleLineCommentChar_iff hok hcp).mpr ⟨c, hc, hnlt, rfl⟩
      by_cases hij1 : j = i + 1
      · subst hij1
        obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.nt hcharNe hdC rfl trivial (.absent .nil))
        exact ⟨_, hd⟩
      · obtain ⟨dtR, hdR⟩ := ih (i := i + 1) (j := j) (by omega) (by omega) hle (fun p hp1 hp2 => hall p (by omega) hp2)
        obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.nt hcharNe hdC rfl trivial (.nt hcharsNe hdR rfl trivial .nil))
        exact ⟨_, hd⟩
  intro i j
  exact ⟨fun ⟨dt, hd⟩ => hfwd (sizeOf dt) (Nat.le_refl _) hd,
         fun ⟨hlt, hle, hall⟩ => hbwd (j - i) rfl hlt hle hall⟩

theorem singleLineComment_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .SingleLineComment [] i j dt) ↔
      (cs[i]? = some 0x2F ∧ cs[i + 1]? = some 0x2F ∧ i + 2 ≤ j ∧ j ≤ Lex.lineEnd cs (i + 2)) := by
  have halts := alts_fixed_eq (cx := cx)
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let s0 : Src := ⟨.lexical, Gen.Lexical.SingleLineComment, 0,
    ⟨[], [.sym (.t (.text "//" false)) false, .sym (.nt .SingleLineCommentChars []) true], none⟩⟩
  have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineComment := by rw [halts]; exact mem_of_get? 0 rfl
  have hcharsNe : (altsOf cx .lexical .SingleLineCommentChars).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
  have ⟨hleMin, hleSz, hleNo, hleAt⟩ := lineEnd_spec cs (i + 2)
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp [srcsOf, writtenAlts, Gen.Lexical.SingleLineComment] at hs
    subst hs
    cases hsw with
    | term ht hr =>
      obtain ⟨hmidEq, hg0, hg1⟩ := termEnd_text_cons (c0 := 0x2F) (csRest := [0x2F]) rfl ht
      have hg1' := hg1 0x2F [] rfl
      have hi2Sz : i + 2 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hg1').1; omega
      have hi2Le := lineEnd_ge_of_le cs hi2Sz
      simp only [List.length_singleton] at hmidEq; subst hmidEq
      cases hr with
      | absent hnil =>
        cases hnil
        exact ⟨hg0, hg1', Nat.le_refl _, hi2Le⟩
      | leaf _ hl _ _ _ => exact nomatch hl
      | nt _ hdR _ _ hnil =>
        cases hnil
        obtain ⟨hltR, hleR, hallR⟩ := (singleLineCommentChars_iff hok hcp).mp ⟨_, hdR⟩
        refine ⟨hg0, hg1', by omega, ?_⟩
        apply Classical.byContradiction; intro hgt
        obtain ⟨ce, hce, hlte⟩ := hleAt (by omega)
        obtain ⟨ce', hce', hnlte⟩ := hallR (Lex.lineEnd cs (i + 2)) hi2Le (by omega)
        rw [hce] at hce'; injection hce' with heq; subst heq; rw [hlte] at hnlte; cases hnlte
  · rintro ⟨hg0, hg1, hij2, hjLe⟩
    obtain ⟨hi2Sz, hex2⟩ := extract_two_eq hg0 hg1
    have ht : Code.termEnd Engine.builder cs (.text "//" false) i = some (i + 2) :=
      termEnd_text_mk "//" false i (by decide) hi2Sz hex2
    by_cases hjeq : j = i + 2
    · subst hjeq
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht (.absent .nil)); exact ⟨_, hd⟩
    · obtain ⟨dtR, hdR⟩ := (singleLineCommentChars_iff hok hcp).mpr
        ⟨by omega, Nat.le_trans hjLe hleSz, fun p hp1 hp2 => hleNo p hp1 (Nat.lt_of_lt_of_le hp2 hjLe)⟩
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht (.nt hcharsNe hdR rfl trivial .nil))
      exact ⟨_, hd⟩

theorem hashbangComment_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .HashbangComment [] i j dt) ↔
      (cs[i]? = some 0x23 ∧ cs[i + 1]? = some 0x21 ∧ i + 2 ≤ j ∧ j ≤ Lex.lineEnd cs (i + 2)) := by
  have halts := alts_fixed_eq (cx := cx)
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let s0 : Src := ⟨.lexical, Gen.Lexical.HashbangComment, 0,
    ⟨[], [.sym (.t (.text "#!" false)) false, .sym (.nt .SingleLineCommentChars []) true], none⟩⟩
  have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .HashbangComment := by rw [halts]; exact mem_of_get? 0 rfl
  have hcharsNe : (altsOf cx .lexical .SingleLineCommentChars).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
  have ⟨hleMin, hleSz, hleNo, hleAt⟩ := lineEnd_spec cs (i + 2)
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp [srcsOf, writtenAlts, Gen.Lexical.HashbangComment] at hs
    subst hs
    cases hsw with
    | term ht hr =>
      obtain ⟨hmidEq, hg0, hg1⟩ := termEnd_text_cons (c0 := 0x23) (csRest := [0x21]) rfl ht
      have hg1' := hg1 0x21 [] rfl
      have hi2Sz : i + 2 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hg1').1; omega
      have hi2Le := lineEnd_ge_of_le cs hi2Sz
      simp only [List.length_singleton] at hmidEq; subst hmidEq
      cases hr with
      | absent hnil =>
        cases hnil
        exact ⟨hg0, hg1', Nat.le_refl _, hi2Le⟩
      | leaf _ hl _ _ _ => exact nomatch hl
      | nt _ hdR _ _ hnil =>
        cases hnil
        obtain ⟨_, _, hallR⟩ := (singleLineCommentChars_iff hok hcp).mp ⟨_, hdR⟩
        refine ⟨hg0, hg1', by omega, ?_⟩
        apply Classical.byContradiction; intro hgt
        obtain ⟨ce, hce, hlte⟩ := hleAt (by omega)
        obtain ⟨ce', hce', hnlte⟩ := hallR (Lex.lineEnd cs (i + 2)) hi2Le (by omega)
        rw [hce] at hce'; injection hce' with heq; subst heq; rw [hlte] at hnlte; cases hnlte
  · rintro ⟨hg0, hg1, hij2, hjLe⟩
    obtain ⟨hi2Sz, hex2⟩ := extract_two_eq hg0 hg1
    have ht : Code.termEnd Engine.builder cs (.text "#!" false) i = some (i + 2) :=
      termEnd_text_mk "#!" false i (by decide) hi2Sz hex2
    by_cases hjeq : j = i + 2
    · subst hjeq
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht (.absent .nil)); exact ⟨_, hd⟩
    · obtain ⟨dtR, hdR⟩ := (singleLineCommentChars_iff hok hcp).mpr
        ⟨by omega, Nat.le_trans hjLe hleSz, fun p hp1 hp2 => hleNo p hp1 (Nat.lt_of_lt_of_le hp2 hjLe)⟩
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht (.nt hcharsNe hdR rfl trivial .nil))
      exact ⟨_, hd⟩

theorem singleLineHTMLOpenComment_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (hhtml : Lex.html cx = true) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .SingleLineHTMLOpenComment [] i j dt) ↔
      (cs[i]? = some 0x3C ∧ cs[i + 1]? = some 0x21 ∧ cs[i + 2]? = some 0x2D ∧ cs[i + 3]? = some 0x2D ∧
       i + 4 ≤ j ∧ j ≤ Lex.lineEnd cs (i + 4)) := by
  have halts : Ecma.Spec.gl.alts cx .lexical .SingleLineHTMLOpenComment = srcsOf .annexB Gen.AnnexB.SingleLineHTMLOpenComment := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.2.1
  let s0 : Src := ⟨.annexB, Gen.AnnexB.SingleLineHTMLOpenComment, 0,
    ⟨[], [.sym (.t (.text "<!--" false)) false, .sym (.nt .SingleLineCommentChars []) true], none⟩⟩
  have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineHTMLOpenComment := by rw [halts]; exact mem_of_get? 0 rfl
  have hcharsNe : (altsOf cx .lexical .SingleLineCommentChars).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
  have ⟨hleMin, hleSz, hleNo, hleAt⟩ := lineEnd_spec cs (i + 4)
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp [srcsOf, writtenAlts, Gen.AnnexB.SingleLineHTMLOpenComment] at hs
    subst hs
    cases hsw with
    | term ht hr =>
      replace ht := lexTerm_eq ht
      unfold Code.termEnd at ht
      dsimp only at ht
      have hw : "<!--".toList.map Char.toNat = [0x3C, 0x21, 0x2D, 0x2D] := rfl
      rw [hw] at ht
      dsimp only [List.length_cons, List.length_nil] at ht
      by_cases hc : (0 < 4 && i + 4 ≤ cs.size &&
          (cs.extract i (i + 4)).toList == [0x3C, 0x21, 0x2D, 0x2D]) = true
      · simp only [hc, ↓reduceIte, Option.some.injEq] at ht
        subst ht
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        obtain ⟨⟨_, hi4Sz⟩, hex⟩ := hc
        rw [extract_toList_eq_slice] at hex
        have hgetAt : ∀ d v, d < 4 → [0x3C, 0x21, 0x2D, 0x2D][d]? = some v → cs[i + d]? = some v := by
          intro d v hd hv
          have hsc : (slice cs.toList i (i + 4))[d]? = some v := by rw [hex]; exact hv
          unfold slice at hsc
          rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at hsc
          simpa using hsc
        have hg0 : cs[i]? = some 0x3C := by simpa using hgetAt 0 0x3C (by omega) rfl
        have hg1 : cs[i + 1]? = some 0x21 := hgetAt 1 0x21 (by omega) rfl
        have hg2 : cs[i + 2]? = some 0x2D := hgetAt 2 0x2D (by omega) rfl
        have hg3 : cs[i + 3]? = some 0x2D := hgetAt 3 0x2D (by omega) rfl
        have hi4Le := lineEnd_ge_of_le cs hi4Sz
        cases hr with
        | absent hnil =>
          cases hnil
          exact ⟨hg0, hg1, hg2, hg3, Nat.le_refl _, hi4Le⟩
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdR _ _ hnil =>
          cases hnil
          obtain ⟨_, _, hallR⟩ := (singleLineCommentChars_iff hok hcp).mp ⟨_, hdR⟩
          refine ⟨hg0, hg1, hg2, hg3, by omega, ?_⟩
          apply Classical.byContradiction; intro hgt
          obtain ⟨ce, hce, hlte⟩ := hleAt (by omega)
          obtain ⟨ce', hce', hnlte⟩ := hallR (Lex.lineEnd cs (i + 4)) hi4Le (by omega)
          rw [hce] at hce'; injection hce' with heq; subst heq; rw [hlte] at hnlte; cases hnlte
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at ht; cases ht
  · rintro ⟨hg0, hg1, hg2, hg3, hij4, hjLe⟩
    obtain ⟨hi4Sz, hex4⟩ := extract_four_eq hg0 hg1 hg2 hg3
    have ht : Code.termEnd Engine.builder cs (.text "<!--" false) i = some (i + 4) :=
      termEnd_text_mk "<!--" false i (by decide) hi4Sz hex4
    by_cases hjeq : j = i + 4
    · subst hjeq
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht (.absent .nil)); exact ⟨_, hd⟩
    · obtain ⟨dtR, hdR⟩ := (singleLineCommentChars_iff hok hcp).mpr
        ⟨by omega, Nat.le_trans hjLe hleSz, fun p hp1 hp2 => hleNo p hp1 (Nat.lt_of_lt_of_le hp2 hjLe)⟩
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term ht (.nt hcharsNe hdR rfl trivial .nil))
      exact ⟨_, hd⟩

private theorem notAsteriskChar_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .MultiLineNotAsteriskChar [] i j dt) ↔
      ∃ c, cs[i]? = some c ∧ c ≠ 0x2A ∧ j = i + 1 := by
  have halts := alts_fixed_eq (cx := cx)
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hscNe : (altsOf cx .lexical .SourceCharacter).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.1 alts_cert_trivia.2.1) rfl
  let s0 : Src := ⟨.lexical, Gen.Lexical.MultiLineNotAsteriskChar, 0,
    ⟨[], [.butNot (.nt .SourceCharacter []) (.sym (.t (.text "*" false)))], none⟩⟩
  have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .MultiLineNotAsteriskChar := by rw [halts]; exact mem_of_get? 0 rfl
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp [srcsOf, writtenAlts, Gen.Lexical.MultiLineNotAsteriskChar] at hs; subst hs
    cases hsw with
    | butNotLeaf _ hl _ _ _ => exact nomatch hl
    | butNotN _ hdSC _ hne hnil =>
      cases hnil
      obtain ⟨c, hc, rfl⟩ := (sourceCharacter_iff hok hcp).mp ⟨_, hdSC⟩
      refine ⟨c, hc, fun hstar => hne ?_, rfl⟩
      subst hstar
      obtain ⟨hi1, hex1⟩ := extract_one_eq hc
      exact termEnd_text_mk "*" false i (by decide) hi1 hex1
  · rintro ⟨c, hc, hneStar, rfl⟩
    obtain ⟨dtSC, hdSC⟩ := (sourceCharacter_iff hok hcp).mpr ⟨c, hc, rfl⟩
    have hne : ¬ (lexSpec cs cx).ExclHolds s0 0 [] i (i + 1) (.sym (.t (.text "*" false))) := by
      intro ht
      obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl ht
      exact hneStar (Option.some.inj (hc.symm.trans hg0))
    obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.butNotN hscNe hdSC rfl hne .nil)
    exact ⟨_, hd⟩

private theorem notSlashOrAsteriskChar_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .MultiLineNotForwardSlashOrAsteriskChar [] i j dt) ↔
      ∃ c, cs[i]? = some c ∧ c ≠ 0x2F ∧ c ≠ 0x2A ∧ j = i + 1 := by
  have halts := alts_fixed_eq (cx := cx)
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hscNe : (altsOf cx .lexical .SourceCharacter).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.1 alts_cert_trivia.2.1) rfl
  let s0 : Src := ⟨.lexical, Gen.Lexical.MultiLineNotForwardSlashOrAsteriskChar, 0,
    ⟨[], [.butNot (.nt .SourceCharacter []) (.oneOf [.t (.text "/" false), .t (.text "*" false)] true)], none⟩⟩
  have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .MultiLineNotForwardSlashOrAsteriskChar := by rw [halts]; exact mem_of_get? 0 rfl
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp [srcsOf, writtenAlts, Gen.Lexical.MultiLineNotForwardSlashOrAsteriskChar] at hs; subst hs
    cases hsw with
    | butNotLeaf _ hl _ _ _ => exact nomatch hl
    | butNotN _ hdSC _ hne hnil =>
      cases hnil
      obtain ⟨c, hc, rfl⟩ := (sourceCharacter_iff hok hcp).mp ⟨_, hdSC⟩
      obtain ⟨hi1, hex1⟩ := extract_one_eq hc
      refine ⟨c, hc, fun h2f => hne ?_, fun h2a => hne ?_, rfl⟩
      · subst h2f; exact ⟨.t (.text "/" false), by simp, termEnd_text_mk "/" false i (by decide) hi1 hex1⟩
      · subst h2a; exact ⟨.t (.text "*" false), by simp, termEnd_text_mk "*" false i (by decide) hi1 hex1⟩
  · rintro ⟨c, hc, hne2f, hne2a, rfl⟩
    obtain ⟨dtSC, hdSC⟩ := (sourceCharacter_iff hok hcp).mpr ⟨c, hc, rfl⟩
    have hne : ¬ (lexSpec cs cx).ExclHolds s0 0 [] i (i + 1) (.oneOf [.t (.text "/" false), .t (.text "*" false)] true) := by
      rintro ⟨y, hy, hsy⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x2F) (csRest := []) rfl hsy
        exact hne2f (Option.some.inj (hc.symm.trans hg0))
      · obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl hsy
        exact hne2a (Option.some.inj (hc.symm.trans hg0))
    obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.butNotN hscNe hdSC rfl hne .nil)
    exact ⟨_, hd⟩

theorem multiLineChars_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {cPos : Nat}
    (hcSz : cPos ≤ cs.size) (hcNotSlash : cs[cPos]? ≠ some 0x2F) :
    ∀ (len : Nat) {p : Nat}, cPos - p = len → p < cPos →
      ((∃ dt, (lexSpec cs cx).PlainDerives .MultiLineCommentChars [] p cPos dt) ↔
        ∀ q, p ≤ q → q < cPos → ¬(cs[q]? = some 0x2A ∧ cs[q + 1]? = some 0x2F)) ∧
      ((∃ dt, (lexSpec cs cx).PlainDerives .PostAsteriskCommentChars [] p cPos dt) ↔
        cs[p]? ≠ some 0x2F ∧ ∀ q, p ≤ q → q < cPos → ¬(cs[q]? = some 0x2A ∧ cs[q + 1]? = some 0x2F)) := by
  have haltsM := alts_fixed_eq (cx := cx)
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.1
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have haltsP := alts_fixed_eq (cx := cx)
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let sm0 : Src := ⟨.lexical, Gen.Lexical.MultiLineCommentChars, 0,
    ⟨[], [.sym (.nt .MultiLineNotAsteriskChar []) false, .sym (.nt .MultiLineCommentChars []) true], none⟩⟩
  let sm1 : Src := ⟨.lexical, Gen.Lexical.MultiLineCommentChars, 1,
    ⟨[], [.sym (.t (.text "*" false)) false, .sym (.nt .PostAsteriskCommentChars []) true], none⟩⟩
  let sp0 : Src := ⟨.lexical, Gen.Lexical.PostAsteriskCommentChars, 0,
    ⟨[], [.sym (.nt .MultiLineNotForwardSlashOrAsteriskChar []) false, .sym (.nt .MultiLineCommentChars []) true], none⟩⟩
  let sp1 : Src := ⟨.lexical, Gen.Lexical.PostAsteriskCommentChars, 1,
    ⟨[], [.sym (.t (.text "*" false)) false, .sym (.nt .PostAsteriskCommentChars []) true], none⟩⟩
  have hsm0 : sm0 ∈ Ecma.Spec.gl.alts cx .lexical .MultiLineCommentChars := by rw [haltsM]; exact mem_of_get? 0 rfl
  have hsm1 : sm1 ∈ Ecma.Spec.gl.alts cx .lexical .MultiLineCommentChars := by rw [haltsM]; exact mem_of_get? 1 rfl
  have hsp0 : sp0 ∈ Ecma.Spec.gl.alts cx .lexical .PostAsteriskCommentChars := by rw [haltsP]; exact mem_of_get? 0 rfl
  have hsp1 : sp1 ∈ Ecma.Spec.gl.alts cx .lexical .PostAsteriskCommentChars := by rw [haltsP]; exact mem_of_get? 1 rfl
  have hneM : (altsOf cx .lexical .MultiLineCommentChars).isEmpty = false := altsOf_nonempty_of_mem hok hsm0
  have hneP : (altsOf cx .lexical .PostAsteriskCommentChars).isEmpty = false := altsOf_nonempty_of_mem hok hsp0
  have hneNA : (altsOf cx .lexical .MultiLineNotAsteriskChar).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
  have hneNSA : (altsOf cx .lexical .MultiLineNotForwardSlashOrAsteriskChar).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
  intro len
  induction len with
  | zero => intro p hlen hp; omega
  | succ len ih =>
    intro p hlen hpLt
    have hpGet : ∃ ch, cs[p]? = some ch := ⟨cs[p]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ch, hch⟩ := hpGet
    obtain ⟨hp1Sz, hex1⟩ := extract_one_eq hch
    by_cases hp1Eq : p + 1 = cPos
    · have hrhsTrue : ∀ q, p ≤ q → q < cPos → ¬(cs[q]? = some 0x2A ∧ cs[q + 1]? = some 0x2F) := by
        intro q hq1 hq2 ⟨_, hb⟩
        have hqc : q + 1 = cPos := by omega
        rw [hqc] at hb; exact hcNotSlash hb
      constructor
      · constructor
        · intro _; exact hrhsTrue
        · intro _
          rw [← hp1Eq]
          by_cases hstar : ch = 0x2A
          · subst hstar
            have ht : Code.termEnd Engine.builder cs (.text "*" false) p = some (p + 1) :=
              termEnd_text_mk "*" false p (by decide) hp1Sz hex1
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsm1 rfl (.term ht (.absent .nil)); exact ⟨_, hd⟩
          · obtain ⟨dt1, hd1⟩ := (notAsteriskChar_iff hok hcp).mpr ⟨ch, hch, hstar, rfl⟩
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsm0 rfl (.nt hneNA hd1 rfl trivial (.absent .nil)); exact ⟨_, hd⟩
      · constructor
        · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
          have hs := lex_mem_alts hok hs
          rw [haltsP] at hs
          simp only [srcsOf, writtenAlts, Gen.Lexical.PostAsteriskCommentChars, List.zipIdx_cons, List.zipIdx_nil,
            List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
          refine ⟨?_, hrhsTrue⟩
          rcases hs with rfl | rfl
          · cases hsw with
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hd1 _ _ _ =>
              obtain ⟨c', hc', hne2f, _, _⟩ := (notSlashOrAsteriskChar_iff hok hcp).mp ⟨_, hd1⟩
              intro hp2f; exact hne2f (Option.some.inj (hc'.symm.trans hp2f))
          · cases hsw with
            | term ht _ =>
              obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl ht
              intro hp2f; rw [hg0] at hp2f; cases hp2f
        · rintro ⟨hpNotSlash, _⟩
          rw [← hp1Eq]
          by_cases hstar : ch = 0x2A
          · subst hstar
            have ht : Code.termEnd Engine.builder cs (.text "*" false) p = some (p + 1) :=
              termEnd_text_mk "*" false p (by decide) hp1Sz hex1
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsp1 rfl (.term ht (.absent .nil)); exact ⟨_, hd⟩
          · have hne2f : ch ≠ 0x2F := fun h => hpNotSlash (h ▸ hch)
            obtain ⟨dt1, hd1⟩ := (notSlashOrAsteriskChar_iff hok hcp).mpr ⟨ch, hch, hne2f, hstar, rfl⟩
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsp0 rfl (.nt hneNSA hd1 rfl trivial (.absent .nil)); exact ⟨_, hd⟩
    · have hp1Lt : p + 1 < cPos := by omega
      have ⟨ihM, ihP⟩ := ih (p := p + 1) (by omega) hp1Lt
      constructor
      · constructor
        · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
          have hs := lex_mem_alts hok hs
          rw [haltsM] at hs
          simp only [srcsOf, writtenAlts, Gen.Lexical.MultiLineCommentChars, List.zipIdx_cons, List.zipIdx_nil,
            List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · cases hsw with
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hd1 _ _ hr =>
              obtain ⟨c', hc', hne2a, rfl⟩ := (notAsteriskChar_iff hok hcp).mp ⟨_, hd1⟩
              cases hr with
              | absent hnil => cases hnil; omega
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdR _ _ hnil =>
                cases hnil
                have hallR := ihM.mp ⟨_, hdR⟩
                intro q hq1 hq2
                by_cases hqp : q = p
                · subst hqp; rintro ⟨ha, _⟩; exact hne2a (Option.some.inj (hc'.symm.trans ha))
                · exact hallR q (by omega) hq2
          · cases hsw with
            | term ht hr =>
              obtain ⟨hmid, _, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl ht
              simp at hmid; subst hmid
              cases hr with
              | absent hnil => cases hnil; omega
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdR _ _ hnil =>
                cases hnil
                obtain ⟨hp1Not2f, hallR⟩ := ihP.mp ⟨_, hdR⟩
                intro q hq1 hq2
                by_cases hqp : q = p
                · subst hqp; rintro ⟨_, hb⟩; exact hp1Not2f hb
                · exact hallR q (by omega) hq2
        · intro hall
          by_cases hstar : ch = 0x2A
          · subst hstar
            have ht : Code.termEnd Engine.builder cs (.text "*" false) p = some (p + 1) :=
              termEnd_text_mk "*" false p (by decide) hp1Sz hex1
            have hp1Not2f : cs[p + 1]? ≠ some 0x2F := fun hb => hall p (Nat.le_refl _) hpLt ⟨hch, hb⟩
            obtain ⟨dtR, hdR⟩ := ihP.mpr ⟨hp1Not2f, fun q hq1 hq2 => hall q (by omega) hq2⟩
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsm1 rfl (.term ht (.nt hneP hdR rfl trivial .nil)); exact ⟨_, hd⟩
          · obtain ⟨dt1, hd1⟩ := (notAsteriskChar_iff hok hcp).mpr ⟨ch, hch, hstar, rfl⟩
            obtain ⟨dtR, hdR⟩ := ihM.mpr (fun q hq1 hq2 => hall q (by omega) hq2)
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsm0 rfl (.nt hneNA hd1 rfl trivial (.nt hneM hdR rfl trivial .nil)); exact ⟨_, hd⟩
      · constructor
        · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
          have hs := lex_mem_alts hok hs
          rw [haltsP] at hs
          simp only [srcsOf, writtenAlts, Gen.Lexical.PostAsteriskCommentChars, List.zipIdx_cons, List.zipIdx_nil,
            List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · cases hsw with
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hd1 _ _ hr =>
              obtain ⟨c', hc', hne2f, hne2a, rfl⟩ := (notSlashOrAsteriskChar_iff hok hcp).mp ⟨_, hd1⟩
              cases hr with
              | absent hnil => cases hnil; omega
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdR _ _ hnil =>
                cases hnil
                have hallR := ihM.mp ⟨_, hdR⟩
                refine ⟨fun hp2f => hne2f (Option.some.inj (hc'.symm.trans hp2f)), fun q hq1 hq2 => ?_⟩
                by_cases hqp : q = p
                · subst hqp; rintro ⟨ha, _⟩; exact hne2a (Option.some.inj (hc'.symm.trans ha))
                · exact hallR q (by omega) hq2
          · cases hsw with
            | term ht hr =>
              obtain ⟨hmid, hg0, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl ht
              simp at hmid; subst hmid
              cases hr with
              | absent hnil => cases hnil; omega
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdR _ _ hnil =>
                cases hnil
                obtain ⟨hp1Not2f, hallR⟩ := ihP.mp ⟨_, hdR⟩
                refine ⟨(fun hp2f => by rw [hg0] at hp2f; cases hp2f), fun q hq1 hq2 => ?_⟩
                by_cases hqp : q = p
                · subst hqp; rintro ⟨_, hb⟩; exact hp1Not2f hb
                · exact hallR q (by omega) hq2
        · rintro ⟨hpNotSlash, hall⟩
          by_cases hstar : ch = 0x2A
          · subst hstar
            have ht : Code.termEnd Engine.builder cs (.text "*" false) p = some (p + 1) :=
              termEnd_text_mk "*" false p (by decide) hp1Sz hex1
            have hp1Not2f : cs[p + 1]? ≠ some 0x2F := fun hb => hall p (Nat.le_refl _) hpLt ⟨hch, hb⟩
            obtain ⟨dtR, hdR⟩ := ihP.mpr ⟨hp1Not2f, fun q hq1 hq2 => hall q (by omega) hq2⟩
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsp1 rfl (.term ht (.nt hneP hdR rfl trivial .nil)); exact ⟨_, hd⟩
          · have hne2f : ch ≠ 0x2F := fun h => hpNotSlash (h ▸ hch)
            obtain ⟨dt1, hd1⟩ := (notSlashOrAsteriskChar_iff hok hcp).mpr ⟨ch, hch, hne2f, hstar, rfl⟩
            obtain ⟨dtR, hdR⟩ := ihM.mpr (fun q hq1 hq2 => hall q (by omega) hq2)
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsp0 rfl (.nt hneNSA hd1 rfl trivial (.nt hneM hdR rfl trivial .nil)); exact ⟨_, hd⟩

private theorem multiLineChars_pos (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {p c : Nat} {dt : DTree}
    (hd : (lexSpec cs cx).PlainDerives .MultiLineCommentChars [] p c dt) : p < c := by
  have haltsM := alts_fixed_eq (cx := cx)
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.1
    alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases hd with
  | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [haltsM] at hs
    simp only [srcsOf, writtenAlts, Gen.Lexical.MultiLineCommentChars, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · cases hsw with
      | leaf _ hl _ _ _ => exact nomatch hl
      | nt _ hd1 _ _ hr =>
        obtain ⟨_, hc1, _, rfl⟩ := (notAsteriskChar_iff hok hcp).mp ⟨_, hd1⟩
        have ⟨hle, _⟩ := lexSeqWith_le hok (extract_one_eq hc1).1 hr
        omega
    · cases hsw with
      | term ht hr =>
        obtain ⟨hmid, _, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl ht
        have ⟨hle, _⟩ := lexSeqWith_le hok (codeTerm_bound Engine.builder cs _ p _ ht).2 hr
        simp at hmid; omega

private theorem slNotAsteriskChar_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (hhtml : Lex.html cx = true) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .SingleLineNotAsteriskChar [] i j dt) ↔
      ∃ c, cs[i]? = some c ∧ c ≠ 0x2A ∧ Lex.isLT c = false ∧ j = i + 1 := by
  have halts : Ecma.Spec.gl.alts cx .lexical .SingleLineNotAsteriskChar = srcsOf .annexB Gen.AnnexB.SingleLineNotAsteriskChar := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.2.2.2.2.2.1
  have hscNe : (altsOf cx .lexical .SourceCharacter).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.1 alts_cert_trivia.2.1) rfl
  have hltNe : (altsOf cx .lexical .LineTerminator).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.2.2.2.2.1 alts_cert_trivia.2.2.2.2.2.1) rfl
  let s0 : Src := ⟨.annexB, Gen.AnnexB.SingleLineNotAsteriskChar, 0,
    ⟨[], [.butNot (.nt .SourceCharacter []) (.oneOf [.t (.text "*" false), .nt .LineTerminator []] true)], none⟩⟩
  have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineNotAsteriskChar := by rw [halts]; exact mem_of_get? 0 rfl
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp [srcsOf, writtenAlts, Gen.AnnexB.SingleLineNotAsteriskChar] at hs; subst hs
    cases hsw with
    | butNotLeaf _ hl _ _ _ => exact nomatch hl
    | butNotN _ hdSC _ hne hnil =>
      cases hnil
      obtain ⟨c, hc, rfl⟩ := (sourceCharacter_iff hok hcp).mp ⟨_, hdSC⟩
      obtain ⟨hi1, hex1⟩ := extract_one_eq hc
      have hne2a : c ≠ 0x2A := fun h2a => by
        subst h2a; exact hne ⟨.t (.text "*" false), by simp, termEnd_text_mk "*" false i (by decide) hi1 hex1⟩
      have hnlt : Lex.isLT c = false := by
        cases hlt : Lex.isLT c with
        | false => rfl
        | true =>
          exfalso; apply hne
          refine ⟨.nt .LineTerminator [], by simp, ?_⟩
          dsimp only [AlphaSpec.SymHolds, lexSpec, codeAlphaSpec, Code.alpha]
          simp only [hltNe, Bool.not_false, ↓reduceIte]
          exact (dec_lineTerminator_iff hok hi1).mpr ⟨c, hc, hlt, rfl⟩
      exact ⟨c, hc, hne2a, hnlt, rfl⟩
  · rintro ⟨c, hc, hne2a, hnlt, rfl⟩
    obtain ⟨dtSC, hdSC⟩ := (sourceCharacter_iff hok hcp).mpr ⟨c, hc, rfl⟩
    obtain ⟨hi1, _⟩ := extract_one_eq hc
    have hne : ¬ (lexSpec cs cx).ExclHolds s0 0 [] i (i + 1)
        (.oneOf [.t (.text "*" false), .nt .LineTerminator []] true) := by
      rintro ⟨y, hy, hsy⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl hsy
        exact hne2a (Option.some.inj (hc.symm.trans hg0))
      · dsimp only [AlphaSpec.SymHolds, lexSpec, codeAlphaSpec, Code.alpha] at hsy
        simp only [hltNe, Bool.not_false, ↓reduceIte] at hsy
        obtain ⟨c', hc', hlt', _⟩ := (dec_lineTerminator_iff hok hi1).mp hsy
        rw [hc] at hc'; injection hc' with hcc; subst hcc; rw [hnlt] at hlt'; cases hlt'
    obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.butNotN hscNe hdSC rfl hne .nil)
    exact ⟨_, hd⟩

private theorem slNotSlashOrAsteriskChar_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (hhtml : Lex.html cx = true) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .SingleLineNotForwardSlashOrAsteriskChar [] i j dt) ↔
      ∃ c, cs[i]? = some c ∧ c ≠ 0x2F ∧ c ≠ 0x2A ∧ Lex.isLT c = false ∧ j = i + 1 := by
  have halts : Ecma.Spec.gl.alts cx .lexical .SingleLineNotForwardSlashOrAsteriskChar =
      srcsOf .annexB Gen.AnnexB.SingleLineNotForwardSlashOrAsteriskChar := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.2.2.2.2.2.2.2.1
  have hscNe : (altsOf cx .lexical .SourceCharacter).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.1 alts_cert_trivia.2.1) rfl
  have hltNe : (altsOf cx .lexical .LineTerminator).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.2.2.2.2.1 alts_cert_trivia.2.2.2.2.2.1) rfl
  let s0 : Src := ⟨.annexB, Gen.AnnexB.SingleLineNotForwardSlashOrAsteriskChar, 0,
    ⟨[], [.butNot (.nt .SourceCharacter []) (.oneOf [.t (.text "/" false), .t (.text "*" false), .nt .LineTerminator []] true)], none⟩⟩
  have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineNotForwardSlashOrAsteriskChar := by rw [halts]; exact mem_of_get? 0 rfl
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp [srcsOf, writtenAlts, Gen.AnnexB.SingleLineNotForwardSlashOrAsteriskChar] at hs; subst hs
    cases hsw with
    | butNotLeaf _ hl _ _ _ => exact nomatch hl
    | butNotN _ hdSC _ hne hnil =>
      cases hnil
      obtain ⟨c, hc, rfl⟩ := (sourceCharacter_iff hok hcp).mp ⟨_, hdSC⟩
      obtain ⟨hi1, hex1⟩ := extract_one_eq hc
      have hne2f : c ≠ 0x2F := fun h2f => by
        subst h2f; exact hne ⟨.t (.text "/" false), by simp, termEnd_text_mk "/" false i (by decide) hi1 hex1⟩
      have hne2a : c ≠ 0x2A := fun h2a => by
        subst h2a; exact hne ⟨.t (.text "*" false), by simp, termEnd_text_mk "*" false i (by decide) hi1 hex1⟩
      have hnlt : Lex.isLT c = false := by
        cases hlt : Lex.isLT c with
        | false => rfl
        | true =>
          exfalso; apply hne
          refine ⟨.nt .LineTerminator [], by simp, ?_⟩
          dsimp only [AlphaSpec.SymHolds, lexSpec, codeAlphaSpec, Code.alpha]
          simp only [hltNe, Bool.not_false, ↓reduceIte]
          exact (dec_lineTerminator_iff hok hi1).mpr ⟨c, hc, hlt, rfl⟩
      exact ⟨c, hc, hne2f, hne2a, hnlt, rfl⟩
  · rintro ⟨c, hc, hne2f, hne2a, hnlt, rfl⟩
    obtain ⟨dtSC, hdSC⟩ := (sourceCharacter_iff hok hcp).mpr ⟨c, hc, rfl⟩
    obtain ⟨hi1, _⟩ := extract_one_eq hc
    have hne : ¬ (lexSpec cs cx).ExclHolds s0 0 [] i (i + 1)
        (.oneOf [.t (.text "/" false), .t (.text "*" false), .nt .LineTerminator []] true) := by
      rintro ⟨y, hy, hsy⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x2F) (csRest := []) rfl hsy
        exact hne2f (Option.some.inj (hc.symm.trans hg0))
      · obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl hsy
        exact hne2a (Option.some.inj (hc.symm.trans hg0))
      · dsimp only [AlphaSpec.SymHolds, lexSpec, codeAlphaSpec, Code.alpha] at hsy
        simp only [hltNe, Bool.not_false, ↓reduceIte] at hsy
        obtain ⟨c', hc', hlt', _⟩ := (dec_lineTerminator_iff hok hi1).mp hsy
        rw [hc] at hc'; injection hc' with hcc; subst hcc; rw [hnlt] at hlt'; cases hlt'
    obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.butNotN hscNe hdSC rfl hne .nil)
    exact ⟨_, hd⟩

theorem slDelimChars_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (hhtml : Lex.html cx = true) {cPos : Nat}
    (hcSz : cPos ≤ cs.size) (hcNotSlash : cs[cPos]? ≠ some 0x2F) :
    ∀ (len : Nat) {p : Nat}, cPos - p = len → p < cPos →
      ((∃ dt, (lexSpec cs cx).PlainDerives .SingleLineDelimitedCommentChars [] p cPos dt) ↔
        ∀ q, p ≤ q → q < cPos → (∃ ch, cs[q]? = some ch ∧ Lex.isLT ch = false) ∧ ¬(cs[q]? = some 0x2A ∧ cs[q + 1]? = some 0x2F)) ∧
      ((∃ dt, (lexSpec cs cx).PlainDerives .SingleLinePostAsteriskCommentChars [] p cPos dt) ↔
        cs[p]? ≠ some 0x2F ∧ ∀ q, p ≤ q → q < cPos → (∃ ch, cs[q]? = some ch ∧ Lex.isLT ch = false) ∧ ¬(cs[q]? = some 0x2A ∧ cs[q + 1]? = some 0x2F)) := by
  have haltsM : Ecma.Spec.gl.alts cx .lexical .SingleLineDelimitedCommentChars =
      srcsOf .annexB Gen.AnnexB.SingleLineDelimitedCommentChars := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.2.2.2.2.1
  have haltsP : Ecma.Spec.gl.alts cx .lexical .SingleLinePostAsteriskCommentChars =
      srcsOf .annexB Gen.AnnexB.SingleLinePostAsteriskCommentChars := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.2.2.2.2.2.2.1
  let sm0 : Src := ⟨.annexB, Gen.AnnexB.SingleLineDelimitedCommentChars, 0,
    ⟨[], [.sym (.nt .SingleLineNotAsteriskChar []) false, .sym (.nt .SingleLineDelimitedCommentChars []) true], none⟩⟩
  let sm1 : Src := ⟨.annexB, Gen.AnnexB.SingleLineDelimitedCommentChars, 1,
    ⟨[], [.sym (.t (.text "*" false)) false, .sym (.nt .SingleLinePostAsteriskCommentChars []) true], none⟩⟩
  let sp0 : Src := ⟨.annexB, Gen.AnnexB.SingleLinePostAsteriskCommentChars, 0,
    ⟨[], [.sym (.nt .SingleLineNotForwardSlashOrAsteriskChar []) false, .sym (.nt .SingleLineDelimitedCommentChars []) true], none⟩⟩
  let sp1 : Src := ⟨.annexB, Gen.AnnexB.SingleLinePostAsteriskCommentChars, 1,
    ⟨[], [.sym (.t (.text "*" false)) false, .sym (.nt .SingleLinePostAsteriskCommentChars []) true], none⟩⟩
  have hsm0 : sm0 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineDelimitedCommentChars := by rw [haltsM]; exact mem_of_get? 0 rfl
  have hsm1 : sm1 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineDelimitedCommentChars := by rw [haltsM]; exact mem_of_get? 1 rfl
  have hsp0 : sp0 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLinePostAsteriskCommentChars := by rw [haltsP]; exact mem_of_get? 0 rfl
  have hsp1 : sp1 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLinePostAsteriskCommentChars := by rw [haltsP]; exact mem_of_get? 1 rfl
  have hneM : (altsOf cx .lexical .SingleLineDelimitedCommentChars).isEmpty = false := altsOf_nonempty_of_mem hok hsm0
  have hneP : (altsOf cx .lexical .SingleLinePostAsteriskCommentChars).isEmpty = false := altsOf_nonempty_of_mem hok hsp0
  have hneNA : (altsOf cx .lexical .SingleLineNotAsteriskChar).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_html_true_eq hhtml alts_cert_annexB.2.2.2.2.2.2.2.1) rfl
  have hneNSA : (altsOf cx .lexical .SingleLineNotForwardSlashOrAsteriskChar).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_html_true_eq hhtml alts_cert_annexB.2.2.2.2.2.2.2.2.2.1) rfl
  intro len
  induction len with
  | zero => intro p hlen hp; omega
  | succ len ih =>
    intro p hlen hpLt
    have hpGet : ∃ ch, cs[p]? = some ch := ⟨cs[p]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ch, hch⟩ := hpGet
    obtain ⟨hp1Sz, hex1⟩ := extract_one_eq hch
    by_cases hp1Eq : p + 1 = cPos
    · constructor
      · constructor
        · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
          have hs := lex_mem_alts hok hs
          rw [haltsM] at hs
          simp only [srcsOf, writtenAlts, Gen.AnnexB.SingleLineDelimitedCommentChars, List.zipIdx_cons,
            List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · cases hsw with
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hd1 _ _ _ =>
              obtain ⟨c', hc', _, hnlt, _⟩ := (slNotAsteriskChar_iff hok hcp hhtml).mp ⟨_, hd1⟩
              intro q hq1 hq2
              have hqp : q = p := by omega
              subst hqp
              exact ⟨⟨c', hc', hnlt⟩, fun ⟨_, hb⟩ => hcNotSlash (hp1Eq ▸ hb)⟩
          · cases hsw with
            | term ht _ =>
              obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl ht
              intro q hq1 hq2
              have hqp : q = p := by omega
              subst hqp
              exact ⟨⟨0x2A, hg0, rfl⟩, fun ⟨_, hb⟩ => hcNotSlash (hp1Eq ▸ hb)⟩
        · intro hall
          obtain ⟨⟨c', hc', hnlt⟩, _⟩ := hall p (Nat.le_refl _) hpLt
          have hceq : ch = c' := Option.some.inj (hch.symm.trans hc'); subst hceq
          rw [← hp1Eq]
          by_cases hstar : ch = 0x2A
          · subst hstar
            have ht : Code.termEnd Engine.builder cs (.text "*" false) p = some (p + 1) :=
              termEnd_text_mk "*" false p (by decide) hp1Sz hex1
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsm1 rfl (.term ht (.absent .nil)); exact ⟨_, hd⟩
          · obtain ⟨dt1, hd1⟩ := (slNotAsteriskChar_iff hok hcp hhtml).mpr ⟨ch, hch, hstar, hnlt, rfl⟩
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsm0 rfl (.nt hneNA hd1 rfl trivial (.absent .nil)); exact ⟨_, hd⟩
      · constructor
        · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
          have hs := lex_mem_alts hok hs
          rw [haltsP] at hs
          simp only [srcsOf, writtenAlts, Gen.AnnexB.SingleLinePostAsteriskCommentChars, List.zipIdx_cons,
            List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · cases hsw with
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hd1 _ _ _ =>
              obtain ⟨c', hc', hne2f, _, hnlt, _⟩ := (slNotSlashOrAsteriskChar_iff hok hcp hhtml).mp ⟨_, hd1⟩
              refine ⟨fun hp2f => hne2f (Option.some.inj (hc'.symm.trans hp2f)), fun q hq1 hq2 => ?_⟩
              have hqp : q = p := by omega
              subst hqp
              exact ⟨⟨c', hc', hnlt⟩, fun ⟨_, hb⟩ => hcNotSlash (hp1Eq ▸ hb)⟩
          · cases hsw with
            | term ht _ =>
              obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl ht
              refine ⟨(fun hp2f => by rw [hg0] at hp2f; cases hp2f), fun q hq1 hq2 => ?_⟩
              have hqp : q = p := by omega
              subst hqp
              exact ⟨⟨0x2A, hg0, rfl⟩, fun ⟨_, hb⟩ => hcNotSlash (hp1Eq ▸ hb)⟩
        · rintro ⟨hpNotSlash, hall⟩
          obtain ⟨⟨c', hc', hnlt⟩, _⟩ := hall p (Nat.le_refl _) hpLt
          have hceq : ch = c' := Option.some.inj (hch.symm.trans hc'); subst hceq
          rw [← hp1Eq]
          by_cases hstar : ch = 0x2A
          · subst hstar
            have ht : Code.termEnd Engine.builder cs (.text "*" false) p = some (p + 1) :=
              termEnd_text_mk "*" false p (by decide) hp1Sz hex1
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsp1 rfl (.term ht (.absent .nil)); exact ⟨_, hd⟩
          · have hne2f : ch ≠ 0x2F := fun h => hpNotSlash (h ▸ hch)
            obtain ⟨dt1, hd1⟩ := (slNotSlashOrAsteriskChar_iff hok hcp hhtml).mpr ⟨ch, hch, hne2f, hstar, hnlt, rfl⟩
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsp0 rfl (.nt hneNSA hd1 rfl trivial (.absent .nil)); exact ⟨_, hd⟩
    · have hp1Lt : p + 1 < cPos := by omega
      have ⟨ihM, ihP⟩ := ih (p := p + 1) (by omega) hp1Lt
      constructor
      · constructor
        · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
          have hs := lex_mem_alts hok hs
          rw [haltsM] at hs
          simp only [srcsOf, writtenAlts, Gen.AnnexB.SingleLineDelimitedCommentChars, List.zipIdx_cons,
            List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · cases hsw with
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hd1 _ _ hr =>
              obtain ⟨c', hc', hne2a, hnlt, rfl⟩ := (slNotAsteriskChar_iff hok hcp hhtml).mp ⟨_, hd1⟩
              cases hr with
              | absent hnil => cases hnil; omega
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdR _ _ hnil =>
                cases hnil
                have hallR := ihM.mp ⟨_, hdR⟩
                intro q hq1 hq2
                by_cases hqp : q = p
                · subst hqp; exact ⟨⟨c', hc', hnlt⟩, fun ⟨ha, _⟩ => hne2a (Option.some.inj (hc'.symm.trans ha))⟩
                · exact hallR q (by omega) hq2
          · cases hsw with
            | term ht hr =>
              obtain ⟨hmid, hg0, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl ht
              simp at hmid; subst hmid
              cases hr with
              | absent hnil => cases hnil; omega
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdR _ _ hnil =>
                cases hnil
                obtain ⟨hp1Not2f, hallR⟩ := ihP.mp ⟨_, hdR⟩
                intro q hq1 hq2
                by_cases hqp : q = p
                · subst hqp; exact ⟨⟨0x2A, hg0, rfl⟩, fun ⟨_, hb⟩ => hp1Not2f hb⟩
                · exact hallR q (by omega) hq2
        · intro hall
          obtain ⟨⟨c', hc', hnlt⟩, hnoClose0⟩ := hall p (Nat.le_refl _) hpLt
          have hceq : ch = c' := Option.some.inj (hch.symm.trans hc'); subst hceq
          by_cases hstar : ch = 0x2A
          · subst hstar
            have ht : Code.termEnd Engine.builder cs (.text "*" false) p = some (p + 1) :=
              termEnd_text_mk "*" false p (by decide) hp1Sz hex1
            have hp1Not2f : cs[p + 1]? ≠ some 0x2F := fun hb => hnoClose0 ⟨hch, hb⟩
            obtain ⟨dtR, hdR⟩ := ihP.mpr ⟨hp1Not2f, fun q hq1 hq2 => hall q (by omega) hq2⟩
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsm1 rfl (.term ht (.nt hneP hdR rfl trivial .nil)); exact ⟨_, hd⟩
          · obtain ⟨dt1, hd1⟩ := (slNotAsteriskChar_iff hok hcp hhtml).mpr ⟨ch, hch, hstar, hnlt, rfl⟩
            obtain ⟨dtR, hdR⟩ := ihM.mpr (fun q hq1 hq2 => hall q (by omega) hq2)
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsm0 rfl (.nt hneNA hd1 rfl trivial (.nt hneM hdR rfl trivial .nil)); exact ⟨_, hd⟩
      · constructor
        · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
          have hs := lex_mem_alts hok hs
          rw [haltsP] at hs
          simp only [srcsOf, writtenAlts, Gen.AnnexB.SingleLinePostAsteriskCommentChars, List.zipIdx_cons,
            List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · cases hsw with
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hd1 _ _ hr =>
              obtain ⟨c', hc', hne2f, hne2a, hnlt, rfl⟩ := (slNotSlashOrAsteriskChar_iff hok hcp hhtml).mp ⟨_, hd1⟩
              cases hr with
              | absent hnil => cases hnil; omega
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdR _ _ hnil =>
                cases hnil
                have hallR := ihM.mp ⟨_, hdR⟩
                refine ⟨fun hp2f => hne2f (Option.some.inj (hc'.symm.trans hp2f)), fun q hq1 hq2 => ?_⟩
                by_cases hqp : q = p
                · subst hqp; exact ⟨⟨c', hc', hnlt⟩, fun ⟨ha, _⟩ => hne2a (Option.some.inj (hc'.symm.trans ha))⟩
                · exact hallR q (by omega) hq2
          · cases hsw with
            | term ht hr =>
              obtain ⟨hmid, hg0, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl ht
              simp at hmid; subst hmid
              cases hr with
              | absent hnil => cases hnil; omega
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdR _ _ hnil =>
                cases hnil
                obtain ⟨hp1Not2f, hallR⟩ := ihP.mp ⟨_, hdR⟩
                refine ⟨(fun hp2f => by rw [hg0] at hp2f; cases hp2f), fun q hq1 hq2 => ?_⟩
                by_cases hqp : q = p
                · subst hqp; exact ⟨⟨0x2A, hg0, rfl⟩, fun ⟨_, hb⟩ => hp1Not2f hb⟩
                · exact hallR q (by omega) hq2
        · rintro ⟨hpNotSlash, hall⟩
          obtain ⟨⟨c', hc', hnlt⟩, hnoClose0⟩ := hall p (Nat.le_refl _) hpLt
          have hceq : ch = c' := Option.some.inj (hch.symm.trans hc'); subst hceq
          by_cases hstar : ch = 0x2A
          · subst hstar
            have ht : Code.termEnd Engine.builder cs (.text "*" false) p = some (p + 1) :=
              termEnd_text_mk "*" false p (by decide) hp1Sz hex1
            have hp1Not2f : cs[p + 1]? ≠ some 0x2F := fun hb => hnoClose0 ⟨hch, hb⟩
            obtain ⟨dtR, hdR⟩ := ihP.mpr ⟨hp1Not2f, fun q hq1 hq2 => hall q (by omega) hq2⟩
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsp1 rfl (.term ht (.nt hneP hdR rfl trivial .nil)); exact ⟨_, hd⟩
          · have hne2f : ch ≠ 0x2F := fun h => hpNotSlash (h ▸ hch)
            obtain ⟨dt1, hd1⟩ := (slNotSlashOrAsteriskChar_iff hok hcp hhtml).mpr ⟨ch, hch, hne2f, hstar, hnlt, rfl⟩
            obtain ⟨dtR, hdR⟩ := ihM.mpr (fun q hq1 hq2 => hall q (by omega) hq2)
            obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsp0 rfl (.nt hneNSA hd1 rfl trivial (.nt hneM hdR rfl trivial .nil)); exact ⟨_, hd⟩

private theorem slDelimChars_pos (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (hhtml : Lex.html cx = true) {p c : Nat} {dt : DTree}
    (hd : (lexSpec cs cx).PlainDerives .SingleLineDelimitedCommentChars [] p c dt) : p < c := by
  have haltsM : Ecma.Spec.gl.alts cx .lexical .SingleLineDelimitedCommentChars =
      srcsOf .annexB Gen.AnnexB.SingleLineDelimitedCommentChars := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.2.2.2.2.1
  cases hd with
  | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [haltsM] at hs
    simp only [srcsOf, writtenAlts, Gen.AnnexB.SingleLineDelimitedCommentChars, List.zipIdx_cons,
      List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · cases hsw with
      | leaf _ hl _ _ _ => exact nomatch hl
      | nt _ hd1 _ _ hr =>
        obtain ⟨_, hc1, _, _, rfl⟩ := (slNotAsteriskChar_iff hok hcp hhtml).mp ⟨_, hd1⟩
        have ⟨hle, _⟩ := lexSeqWith_le hok (extract_one_eq hc1).1 hr
        omega
    · cases hsw with
      | term ht hr =>
        obtain ⟨hmid, _, _⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := []) rfl ht
        have ⟨hle, _⟩ := lexSeqWith_le hok (codeTerm_bound Engine.builder cs _ p _ ht).2 hr
        simp at hmid; omega

private theorem closeAt_eq_some_of_no_earlier {cs : Array Nat} {k c : Nat}
    (hle : k ≤ c) (hc0 : cs[c]? = some 0x2A) (hc1 : cs[c + 1]? = some 0x2F)
    (hno : ∀ q, k ≤ q → q < c → ¬(cs[q]? = some 0x2A ∧ cs[q + 1]? = some 0x2F)) :
    Lex.closeAt cs k = some c := by
  have hlt1 : c + 1 < cs.size := (Array.getElem?_eq_some_iff.mp hc1).1
  rcases opt_none_or_some (Lex.closeAt cs k) with hnone | ⟨c', hc'⟩
  · exfalso; exact closeAt_none_spec cs k hnone c hle hlt1 ⟨hc0, hc1⟩
  · rw [hc']; congr 1
    obtain ⟨hkc', _, hc'0, hc'1, hno'⟩ := closeAt_some_spec cs k c' hc'
    by_cases hlt : c' < c
    · exact absurd ⟨hc'0, hc'1⟩ (hno c' hkc' hlt)
    · by_cases hgt : c < c'
      · exact absurd ⟨hc0, hc1⟩ (hno' c hle hgt)
      · omega

private theorem unpack_seq_opt_nt {cx : Ctx} {cs : Array Nat} {s : Src} {ps : List Param} {k : Nat}
    {n : NT} {args : List Arg} {is : List Item} {i j : Nat} {m : List Bool} {ts : List DTree}
    (hsw : (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) s ps k (.sym (.nt n args) true :: is) i j m ts) :
    (∃ m', m = false :: m' ∧ (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) s ps (k + 1) is i j m' ts) ∨
    (∃ hMid dt m' ts', m = true :: m' ∧ ts = dt :: ts' ∧
      (lexSpec cs cx).PlainDerives n (applyArgs ps args) i hMid dt ∧
      (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) s ps (k + 1) is hMid j m' ts') := by
  cases hsw with
  | absent hr => exact Or.inl ⟨_, rfl, hr⟩
  | leaf _ hl _ _ _ => exact nomatch hl
  | nt _ hd _ _ hr => exact Or.inr ⟨_, _, _, _, rfl, rfl, hd, hr⟩

theorem singleLineDelimitedComment_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (hhtml : Lex.html cx = true) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .SingleLineDelimitedComment [] i j dt) ↔
      (cs[i]? = some 0x2F ∧ cs[i + 1]? = some 0x2A ∧
       ∃ c, Lex.closeAt cs (i + 2) = some c ∧ (cs.extract (i + 2) c).any Lex.isLT = false ∧ j = c + 2) := by
  have halts : Ecma.Spec.gl.alts cx .lexical .SingleLineDelimitedComment =
      srcsOf .annexB Gen.AnnexB.SingleLineDelimitedComment := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.2.2.2.1
  let s0 : Src := ⟨.annexB, Gen.AnnexB.SingleLineDelimitedComment, 0,
    ⟨[], [.sym (.t (.text "/*" false)) false, .sym (.nt .SingleLineDelimitedCommentChars []) true, .sym (.t (.text "*/" false)) false], none⟩⟩
  have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineDelimitedComment := by rw [halts]; exact mem_of_get? 0 rfl
  have hneChars : (altsOf cx .lexical .SingleLineDelimitedCommentChars).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_html_true_eq hhtml alts_cert_annexB.2.2.2.2.2.2.1) rfl
  constructor
  · rintro ⟨_, hd⟩; cases hd with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [halts] at hs
    simp [srcsOf, writtenAlts, Gen.AnnexB.SingleLineDelimitedComment] at hs; subst hs
    cases hsw with
    | term htOpen hr =>
      obtain ⟨hmidO, hg0, hg1f⟩ := termEnd_text_cons (c0 := 0x2F) (csRest := [0x2A]) rfl htOpen
      have hg1 := hg1f 0x2A [] rfl
      simp at hmidO; subst hmidO
      rcases unpack_seq_opt_nt hr with ⟨_, _, hr2⟩ | ⟨hMid, _, _, _, _, _, hdChars, hr2⟩
      · cases hr2 with
        | term htClose hnil =>
          cases hnil
          obtain ⟨hjEq, hc0, hc1f⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := [0x2F]) rfl htClose
          have hc1 := hc1f 0x2F [] rfl
          simp at hjEq
          have hcl := closeAt_eq_some_of_no_earlier (Nat.le_refl _) hc0 hc1 (fun _ h1 h2 => by omega)
          have hnoLt : (cs.extract (i + 2) (i + 2)).any Lex.isLT = false := by
            rw [Bool.eq_false_iff, ne_eq, extract_any_isLT_iff cs (by have := (Array.getElem?_eq_some_iff.mp hc0).1; omega)]
            rintro ⟨p, _, hp1, hp2, _⟩; omega
          exact ⟨hg0, hg1, i + 2, hcl, hnoLt, by omega⟩
      · cases hr2 with
        | term htClose hnil =>
          cases hnil
          obtain ⟨hjEq, hc0, hc1f⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := [0x2F]) rfl htClose
          have hc1 := hc1f 0x2F [] rfl
          simp at hjEq
          have hcSz : hMid ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hc0).1; omega
          have hcNot2f : cs[hMid]? ≠ some 0x2F := by rw [hc0]; decide
          have hpLt := slDelimChars_pos hok hcp hhtml hdChars
          have hall := (slDelimChars_iff hok hcp hhtml hcSz hcNot2f (hMid - (i + 2)) rfl hpLt).1.mp ⟨_, hdChars⟩
          have hcl := closeAt_eq_some_of_no_earlier (Nat.le_of_lt hpLt) hc0 hc1 (fun q hq1 hq2 => (hall q hq1 hq2).2)
          have hnoLt : (cs.extract (i + 2) hMid).any Lex.isLT = false := by
            rw [Bool.eq_false_iff, ne_eq, extract_any_isLT_iff cs hcSz]
            rintro ⟨q, ch, hq1, hq2, hqGet, hqLt⟩
            obtain ⟨⟨ch', hqGet', hqNoLt⟩, _⟩ := hall q hq1 hq2
            rw [hqGet] at hqGet'; injection hqGet' with heq; subst heq; rw [hqLt] at hqNoLt; cases hqNoLt
          exact ⟨hg0, hg1, hMid, hcl, hnoLt, by omega⟩
  · rintro ⟨hg0, hg1, c, hcl, hnoLt, rfl⟩
    obtain ⟨hi2c, hc1Sz, hc0, hc1, hnoEarlier⟩ := closeAt_some_spec cs (i + 2) c hcl
    obtain ⟨hi2Sz, hexO⟩ := extract_two_eq hg0 hg1
    obtain ⟨hc2Sz, hexC⟩ := extract_two_eq hc0 hc1
    have htO := termEnd_text_mk "/*" false i (by decide) hi2Sz hexO
    have htC := termEnd_text_mk "*/" false c (by decide) hc2Sz hexC
    by_cases hce : c = i + 2
    · subst hce
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term htO (.absent (.term htC .nil))); exact ⟨_, hd⟩
    · have hcSz : c ≤ cs.size := by omega
      have hcNot2f : cs[c]? ≠ some 0x2F := by rw [hc0]; decide
      have hall : ∀ q, i + 2 ≤ q → q < c → (∃ ch, cs[q]? = some ch ∧ Lex.isLT ch = false) ∧ ¬(cs[q]? = some 0x2A ∧ cs[q + 1]? = some 0x2F) := by
        intro q hq1 hq2
        have hqGet : cs[q]? = some (cs[q]'(by omega)) := Array.getElem?_eq_getElem (by omega)
        have hqNoLt : Lex.isLT (cs[q]'(by omega)) = false := by
          cases hl : Lex.isLT (cs[q]'(by omega)) with
          | false => rfl
          | true =>
            have hexT : (cs.extract (i + 2) c).any Lex.isLT = true :=
              (extract_any_isLT_iff cs hcSz).mpr ⟨q, cs[q]'(by omega), hq1, hq2, hqGet, hl⟩
            rw [hnoLt] at hexT; cases hexT
        exact ⟨⟨_, hqGet, hqNoLt⟩, hnoEarlier q hq1 hq2⟩
      obtain ⟨dtCh, hdCh⟩ := (slDelimChars_iff hok hcp hhtml hcSz hcNot2f (c - (i + 2)) rfl (by omega)).1.mpr hall
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.term htO (.nt hneChars hdCh rfl trivial (.term htC .nil)))
      exact ⟨_, hd⟩

theorem whiteSpaceSequence_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hhtml : Lex.html cx = true) :
    ∀ {i j : Nat},
      (∃ dt, (lexSpec cs cx).PlainDerives .WhiteSpaceSequence [] i j dt) ↔
        (i < j ∧ j ≤ cs.size ∧ ∀ p, i ≤ p → p < j → ∃ c, cs[p]? = some c ∧ Lex.isWS Engine.builder c = true) := by
  have halts : Ecma.Spec.gl.alts cx .lexical .WhiteSpaceSequence = srcsOf .annexB Gen.AnnexB.WhiteSpaceSequence := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.2.2.2.2.2.2.2.2.1
  let s0 : Src := ⟨.annexB, Gen.AnnexB.WhiteSpaceSequence, 0,
    ⟨[], [.sym (.nt .WhiteSpace []) false, .sym (.nt .WhiteSpaceSequence []) true], none⟩⟩
  have hs0 : s0 ∈ Ecma.Spec.gl.alts cx .lexical .WhiteSpaceSequence := by rw [halts]; exact mem_of_get? 0 rfl
  have hwsNe : (altsOf cx .lexical .WhiteSpace).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.2.2.1 alts_cert_trivia.2.2.2.1) rfl
  have hseqNe : (altsOf cx .lexical .WhiteSpaceSequence).isEmpty = false := altsOf_nonempty_of_mem hok hs0
  have hfwd : ∀ (sz : Nat) {i j : Nat} {dt : DTree}, sizeOf dt ≤ sz →
      (lexSpec cs cx).PlainDerives .WhiteSpaceSequence [] i j dt →
      i < j ∧ j ≤ cs.size ∧ ∀ p, i ≤ p → p < j → ∃ c, cs[p]? = some c ∧ Lex.isWS Engine.builder c = true := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ih =>
      intro i j dt hsz hd
      cases hd with
      | node s hs _ _ _ hsw =>
        have hs := lex_mem_alts hok hs
        rw [halts] at hs
        simp [srcsOf, writtenAlts, Gen.AnnexB.WhiteSpaceSequence] at hs; subst hs
        cases hsw with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdW _ _ hr =>
          obtain ⟨c, hc, hws, rfl⟩ := (whiteSpace_iff hok).mp ⟨_, hdW⟩
          have hi1 : i + 1 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hc).1; omega
          cases hr with
          | absent hnil =>
            cases hnil
            exact ⟨by omega, hi1, fun p hp1 hp2 => by rw [show p = i from by omega]; exact ⟨c, hc, hws⟩⟩
          | leaf _ hl _ _ _ => exact nomatch hl
          | nt _ hdR _ _ hnil =>
            cases hnil
            have ⟨hltR, hleR, hallR⟩ := ih (sz - 1)
              (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega)
              (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega) hdR
            refine ⟨by omega, hleR, fun p hp1 hp2 => ?_⟩
            by_cases hpi : p = i
            · subst hpi; exact ⟨c, hc, hws⟩
            · exact hallR p (by omega) hp2
  have hbwd : ∀ (len : Nat) {i j : Nat}, j - i = len →
      i < j → j ≤ cs.size → (∀ p, i ≤ p → p < j → ∃ c, cs[p]? = some c ∧ Lex.isWS Engine.builder c = true) →
      ∃ dt, (lexSpec cs cx).PlainDerives .WhiteSpaceSequence [] i j dt := by
    intro len
    induction len with
    | zero => intro _ _ hlen hlt; omega
    | succ len ih =>
      intro i j hlen hlt hle hall
      obtain ⟨c, hc, hws⟩ := hall i (Nat.le_refl _) hlt
      obtain ⟨dtW, hdW⟩ := (whiteSpace_iff hok).mpr ⟨c, hc, hws, rfl⟩
      by_cases hij1 : j = i + 1
      · subst hij1
        obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.nt hwsNe hdW rfl trivial (.absent .nil)); exact ⟨_, hd⟩
      · obtain ⟨dtR, hdR⟩ := ih (i := i + 1) (j := j) (by omega) (by omega) hle (fun p hp1 hp2 => hall p (by omega) hp2)
        obtain ⟨_, hd⟩ := mkLexPlainSimple hok hs0 rfl (.nt hwsNe hdW rfl trivial (.nt hseqNe hdR rfl trivial .nil))
        exact ⟨_, hd⟩
  intro i j
  exact ⟨fun ⟨dt, hd⟩ => hfwd (sizeOf dt) (Nat.le_refl _) hd,
         fun ⟨hlt, hle, hall⟩ => hbwd (j - i) rfl hlt hle hall⟩

/-! ## `HTMLCloseComment` (`Lex.htmlClose`) -/

theorem htmlClose_spec (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (hhtml : Lex.html cx = true) :
    ∀ (k : Nat),
      (∀ e, Lex.htmlClose Engine.builder cs k = some e →
        k + 3 ≤ e ∧ e ≤ cs.size ∧
        (∃ dt, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k e dt) ∧
        (∀ j dt, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k j dt → j ≤ e)) ∧
      (Lex.htmlClose Engine.builder cs k = none →
        ∀ j dt, ¬ (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k j dt) := by
  have haltsHC : Ecma.Spec.gl.alts cx .lexical .HTMLCloseComment = srcsOf .annexB Gen.AnnexB.HTMLCloseComment := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.1
  have haltsSeq : Ecma.Spec.gl.alts cx .lexical .SingleLineDelimitedCommentSequence =
      srcsOf .annexB Gen.AnnexB.SingleLineDelimitedCommentSequence := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.2.2.2.2.2.2.2.2.2
  let sHC : Src := ⟨.annexB, Gen.AnnexB.HTMLCloseComment, 0,
    ⟨[], [.sym (.nt .WhiteSpaceSequence []) true, .sym (.nt .SingleLineDelimitedCommentSequence []) true,
          .sym (.t (.text "-->" false)) false, .sym (.nt .SingleLineCommentChars []) true], none⟩⟩
  let sSeq : Src := ⟨.annexB, Gen.AnnexB.SingleLineDelimitedCommentSequence, 0,
    ⟨[], [.sym (.nt .SingleLineDelimitedComment []) false, .sym (.nt .WhiteSpaceSequence []) true,
          .sym (.nt .SingleLineDelimitedCommentSequence []) true], none⟩⟩
  have hsHC : sHC ∈ Ecma.Spec.gl.alts cx .lexical .HTMLCloseComment := by rw [haltsHC]; exact mem_of_get? 0 rfl
  have hsSeq : sSeq ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineDelimitedCommentSequence := by rw [haltsSeq]; exact mem_of_get? 0 rfl
  have hneWSS : (altsOf cx .lexical .WhiteSpaceSequence).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_html_true_eq hhtml alts_cert_annexB.2.2.2.2.2.2.2.2.2.2.1) rfl
  have hneSeq : (altsOf cx .lexical .SingleLineDelimitedCommentSequence).isEmpty = false := altsOf_nonempty_of_mem hok hsSeq
  have hneDelim : (altsOf cx .lexical .SingleLineDelimitedComment).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_html_true_eq hhtml alts_cert_annexB.2.2.2.2.2.1) rfl
  have hneSLC : (altsOf cx .lexical .SingleLineCommentChars).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
  have hunpack : ∀ {k j : Nat} {dt : DTree},
      (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k j dt →
      let w := Lex.wsEnd Engine.builder cs k
      (cs[w]? = some 0x2D ∧ cs[w + 1]? = some 0x2D ∧ cs[w + 2]? = some 0x3E ∧ w + 3 ≤ j ∧ j ≤ Lex.lineEnd cs (w + 3)) ∨
      (cs[w]? = some 0x2F ∧ cs[w + 1]? = some 0x2A ∧
       ∃ c dt', Lex.closeAt cs (w + 2) = some c ∧ (cs.extract (w + 2) c).any Lex.isLT = false ∧
         k < c + 2 ∧ c + 2 ≤ cs.size ∧ (lexSpec cs cx).PlainDerives .HTMLCloseComment [] (c + 2) j dt') := by
    intro k j dt hd
    let w := Lex.wsEnd Engine.builder cs k
    have ⟨hkw, _, hwAll, hwStop⟩ := wsEnd_spec cs k
    cases hd with
    | node s hs _ _ _ hsw =>
      have hs := lex_mem_alts hok hs
      rw [haltsHC] at hs
      simp [srcsOf, writtenAlts, Gen.AnnexB.HTMLCloseComment] at hs; subst hs
      have hafterWS : ∀ {w0 : Nat} {m1 : List Bool} {ts1 : List DTree},
          (w0 = k ∨ (k < w0 ∧ w0 ≤ cs.size ∧ ∀ p, k ≤ p → p < w0 → ∃ ch, cs[p]? = some ch ∧ Lex.isWS Engine.builder ch = true)) →
          (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sHC [] 1
            [.sym (.nt .SingleLineDelimitedCommentSequence []) true,
             .sym (.t (.text "-->" false)) false,
             .sym (.nt .SingleLineCommentChars []) true] w0 j m1 ts1 →
          (cs[w]? = some 0x2D ∧ cs[w + 1]? = some 0x2D ∧ cs[w + 2]? = some 0x3E ∧ w + 3 ≤ j ∧ j ≤ Lex.lineEnd cs (w + 3)) ∨
          (cs[w]? = some 0x2F ∧ cs[w + 1]? = some 0x2A ∧
           ∃ c dt', Lex.closeAt cs (w + 2) = some c ∧ (cs.extract (w + 2) c).any Lex.isLT = false ∧
             k < c + 2 ∧ c + 2 ≤ cs.size ∧ (lexSpec cs cx).PlainDerives .HTMLCloseComment [] (c + 2) j dt') := by
        intro w0 m1 ts1 hw0 hr1
        have hw0Eq : cs[w0]? = some 0x2D ∨ cs[w0]? = some 0x2F → w0 = w := by
          intro h2df
          have hw0NotWS : ∀ ch, cs[w0]? = some ch → Lex.isWS Engine.builder ch = false := by
            intro ch hch
            cases hws : Lex.isWS Engine.builder ch with
            | false => rfl
            | true =>
              obtain ⟨hne2f, hne2d, _⟩ := isWS_ne hws
              rcases h2df with h | h
              · exact absurd (Option.some.inj (hch.symm.trans h)) hne2d
              · exact absurd (Option.some.inj (hch.symm.trans h)) hne2f
          rcases hw0 with rfl | ⟨_, _, hw0All⟩
          · by_cases hlt : w0 < w
            · obtain ⟨ch, hch, hws⟩ := hwAll w0 (Nat.le_refl _) hlt
              rw [hw0NotWS ch hch] at hws; cases hws
            · omega
          · by_cases hlt : w0 < w
            · obtain ⟨ch, hch, hws⟩ := hwAll w0 (by omega) hlt
              rw [hw0NotWS ch hch] at hws; cases hws
            · by_cases hgt : w < w0
              · obtain ⟨ch, hch, hnws⟩ := hwStop (by omega)
                obtain ⟨ch', hch', hws⟩ := hw0All w hkw hgt
                rw [hch] at hch'; injection hch' with heq; subst heq; rw [hnws] at hws; cases hws
              · omega
        cases hr1 with
        | absent hr2 =>
          cases hr2 with
          | term htClose hr3 =>
            have hw3 : "-->".toList.map Char.toNat = [0x2D, 0x2D, 0x3E] := rfl
            obtain ⟨hmidEq, hg0, hg1f⟩ := termEnd_text_cons hw3 htClose
            have hg1 := hg1f 0x2D [0x3E] rfl
            have hg2 : cs[w0 + 2]? = some 0x3E := by
              replace htClose := lexTerm_eq htClose
              unfold Code.termEnd at htClose; dsimp only at htClose; rw [hw3] at htClose
              by_cases hc : (0 < ([0x2D, 0x2D, 0x3E] : List Nat).length && w0 + 3 ≤ cs.size &&
                  (cs.extract w0 (w0 + 3)).toList == [0x2D, 0x2D, 0x3E]) = true
              · simp only [Bool.and_eq_true, beq_iff_eq] at hc
                have hex := hc.2; rw [extract_toList_eq_slice] at hex
                have hsc : (slice cs.toList w0 (w0 + 3))[2]? = some 0x3E := by rw [hex]; rfl
                unfold slice at hsc
                rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at hsc
                simpa using hsc
              · simp only [List.length_cons, List.length_nil] at htClose hc
                simp only [hc, Bool.false_eq_true, ↓reduceIte] at htClose; cases htClose
            have hweq := hw0Eq (Or.inl hg0)
            subst hweq
            simp at hmidEq; subst hmidEq
            have hw3Sz : w + 3 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hg2).1; omega
            have ⟨_, _, _, hleAt⟩ := lineEnd_spec cs (w + 3)
            have hw3Le := lineEnd_ge_of_le cs hw3Sz
            cases hr3 with
            | absent hnil =>
              cases hnil
              exact Or.inl ⟨hg0, hg1, hg2, Nat.le_refl _, hw3Le⟩
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hdSLC _ _ hnil =>
              cases hnil
              obtain ⟨_, _, hallR⟩ := (singleLineCommentChars_iff hok hcp).mp ⟨_, hdSLC⟩
              refine Or.inl ⟨hg0, hg1, hg2, by omega, ?_⟩
              apply Classical.byContradiction; intro hgt
              obtain ⟨ce, hce, hlte⟩ := hleAt (by omega)
              obtain ⟨ce', hce', hnlte⟩ := hallR (Lex.lineEnd cs (w + 3)) hw3Le (by omega)
              rw [hce] at hce'; injection hce' with heq; subst heq; rw [hlte] at hnlte; cases hnlte
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdSeq _ _ hr2 =>
          cases hdSeq with
          | node ss hss _ _ _ hswSeq =>
            have hss := lex_mem_alts hok hss
            rw [haltsSeq] at hss
            simp [srcsOf, writtenAlts, Gen.AnnexB.SingleLineDelimitedCommentSequence] at hss; subst hss
            cases hswSeq with
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hdDelim _ _ hrSeq1 =>
              obtain ⟨hg0, hg1, c, hcl, hnoLt, rfl⟩ := (singleLineDelimitedComment_iff hok hcp hhtml).mp ⟨_, hdDelim⟩
              have hweq := hw0Eq (Or.inr hg0)
              subst hweq
              obtain ⟨hw2c, hc1Sz, _, _, _⟩ := closeAt_some_spec cs (w + 2) c hcl
              cases hrSeq1 with
              | absent hrSeq2 =>
                cases hrSeq2 with
                | absent hnilSeq =>
                  cases hnilSeq
                  obtain ⟨_, hdSub⟩ := mkLexPlainSimple hok hsHC rfl (.absent (.absent hr2))
                  exact Or.inr ⟨hg0, hg1, c, _, hcl, hnoLt, by omega, by omega, hdSub⟩
                | leaf _ hl _ _ _ => exact nomatch hl
                | nt _ hdSeqSub _ _ hnilSeq =>
                  cases hnilSeq
                  obtain ⟨_, hdSub⟩ := mkLexPlainSimple hok hsHC rfl (.absent (.nt hneSeq hdSeqSub rfl trivial hr2))
                  exact Or.inr ⟨hg0, hg1, c, _, hcl, hnoLt, by omega, by omega, hdSub⟩
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdWS2 _ _ hrSeq2 =>
                cases hrSeq2 with
                | absent hnilSeq =>
                  cases hnilSeq
                  obtain ⟨_, hdSub⟩ := mkLexPlainSimple hok hsHC rfl (.nt hneWSS hdWS2 rfl trivial (.absent hr2))
                  exact Or.inr ⟨hg0, hg1, c, _, hcl, hnoLt, by omega, by omega, hdSub⟩
                | leaf _ hl _ _ _ => exact nomatch hl
                | nt _ hdSeqSub _ _ hnilSeq =>
                  cases hnilSeq
                  obtain ⟨_, hdSub⟩ := mkLexPlainSimple hok hsHC rfl
                    (.nt hneWSS hdWS2 rfl trivial (.nt hneSeq hdSeqSub rfl trivial hr2))
                  exact Or.inr ⟨hg0, hg1, c, _, hcl, hnoLt, by omega, by omega, hdSub⟩
      cases hsw with
      | absent hr1 => exact hafterWS (Or.inl rfl) hr1
      | leaf _ hl _ _ _ => exact nomatch hl
      | nt _ hdWS _ _ hr1 =>
        exact hafterWS (Or.inr ((whiteSpaceSequence_iff hok hhtml).mp ⟨_, hdWS⟩)) hr1
  have hpackArrow : ∀ {k : Nat},
      cs[Lex.wsEnd Engine.builder cs k]? = some 0x2D →
      cs[Lex.wsEnd Engine.builder cs k + 1]? = some 0x2D →
      cs[Lex.wsEnd Engine.builder cs k + 2]? = some 0x3E →
      ∃ dt, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k (Lex.lineEnd cs (Lex.wsEnd Engine.builder cs k + 3)) dt := by
    intro k hg0 hg1 hg2
    let w := Lex.wsEnd Engine.builder cs k
    change cs[w]? = some 0x2D at hg0
    change cs[w + 1]? = some 0x2D at hg1
    change cs[w + 2]? = some 0x3E at hg2
    change ∃ dt, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k (Lex.lineEnd cs (w + 3)) dt
    have ⟨hkw, _, hwAll, _⟩ := wsEnd_spec cs k
    obtain ⟨hw3Sz, hex3⟩ := extract_three_eq hg0 hg1 hg2
    have htArrow := termEnd_text_mk "-->" false w (by decide) hw3Sz hex3
    have ⟨_, hleSz, hleNo, _⟩ := lineEnd_spec cs (w + 3)
    have hw3Le := lineEnd_ge_of_le cs hw3Sz
    have htail : ∃ m3 ts3, (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sHC [] 3
        [.sym (.nt .SingleLineCommentChars []) true] (w + 3) (Lex.lineEnd cs (w + 3)) m3 ts3 := by
      by_cases heq : Lex.lineEnd cs (w + 3) = w + 3
      · rw [heq]; exact ⟨_, _, .absent .nil⟩
      · obtain ⟨dtC, hdC⟩ := (singleLineCommentChars_iff hok hcp).mpr ⟨by omega, hleSz, hleNo⟩
        exact ⟨_, _, .nt hneSLC hdC rfl trivial .nil⟩
    obtain ⟨_, _, hsw3⟩ := htail
    by_cases hwk : w = k
    · rw [hwk] at hsw3 htArrow ⊢
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsHC rfl (.absent (.absent (.term htArrow hsw3))); exact ⟨_, hd⟩
    · obtain ⟨dtWS, hdWS⟩ := (whiteSpaceSequence_iff hok hhtml).mpr ⟨by omega, by omega, hwAll⟩
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsHC rfl (.nt hneWSS hdWS rfl trivial (.absent (.term htArrow hsw3)))
      exact ⟨_, hd⟩
  have hpackDelim : ∀ {k c e : Nat} {dtSub : DTree},
      cs[Lex.wsEnd Engine.builder cs k]? = some 0x2F →
      cs[Lex.wsEnd Engine.builder cs k + 1]? = some 0x2A →
      Lex.closeAt cs (Lex.wsEnd Engine.builder cs k + 2) = some c →
      (cs.extract (Lex.wsEnd Engine.builder cs k + 2) c).any Lex.isLT = false →
      (lexSpec cs cx).PlainDerives .HTMLCloseComment [] (c + 2) e dtSub →
      ∃ dt, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k e dt := by
    intro k c e dtSub hg0 hg1 hcl hnoLt hdSub
    let w := Lex.wsEnd Engine.builder cs k
    change cs[w]? = some 0x2F at hg0
    change cs[w + 1]? = some 0x2A at hg1
    change Lex.closeAt cs (w + 2) = some c at hcl
    change (cs.extract (w + 2) c).any Lex.isLT = false at hnoLt
    have ⟨hkw, _, hwAll, _⟩ := wsEnd_spec cs k
    have hwSz : w < cs.size := (Array.getElem?_eq_some_iff.mp hg0).1
    obtain ⟨dtD, hdD⟩ := (singleLineDelimitedComment_iff hok hcp hhtml).mpr ⟨hg0, hg1, c, hcl, hnoLt, rfl⟩
    cases hdSub with
    | node s hs _ _ _ hswSub =>
      have hs := lex_mem_alts hok hs
      rw [haltsHC] at hs
      simp [srcsOf, writtenAlts, Gen.AnnexB.HTMLCloseComment] at hs; subst hs
      have hseqFromW : ∃ m1 ts1, (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sHC [] 1
          [.sym (.nt .SingleLineDelimitedCommentSequence []) true,
           .sym (.t (.text "-->" false)) false,
           .sym (.nt .SingleLineCommentChars []) true] w e m1 ts1 := by
        cases hswSub with
        | absent hr1 =>
          cases hr1 with
          | absent hr2 =>
            obtain ⟨_, hdS⟩ := mkLexPlainSimple hok hsSeq rfl (.nt hneDelim hdD rfl trivial (.absent (.absent .nil)))
            exact ⟨_, _, .nt hneSeq hdS rfl trivial hr2⟩
          | leaf _ hl _ _ _ => exact nomatch hl
          | nt _ hdS2 _ _ hr2 =>
            obtain ⟨_, hdS⟩ := mkLexPlainSimple hok hsSeq rfl (.nt hneDelim hdD rfl trivial (.absent (.nt hneSeq hdS2 rfl trivial .nil)))
            exact ⟨_, _, .nt hneSeq hdS rfl trivial hr2⟩
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdWS2 _ _ hr1 =>
          cases hr1 with
          | absent hr2 =>
            obtain ⟨_, hdS⟩ := mkLexPlainSimple hok hsSeq rfl (.nt hneDelim hdD rfl trivial (.nt hneWSS hdWS2 rfl trivial (.absent .nil)))
            exact ⟨_, _, .nt hneSeq hdS rfl trivial hr2⟩
          | leaf _ hl _ _ _ => exact nomatch hl
          | nt _ hdS2 _ _ hr2 =>
            obtain ⟨_, hdS⟩ := mkLexPlainSimple hok hsSeq rfl
              (.nt hneDelim hdD rfl trivial (.nt hneWSS hdWS2 rfl trivial (.nt hneSeq hdS2 rfl trivial .nil)))
            exact ⟨_, _, .nt hneSeq hdS rfl trivial hr2⟩
      obtain ⟨_, _, hsw1⟩ := hseqFromW
      by_cases hwk : w = k
      · rw [hwk] at hsw1
        obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsHC rfl (.absent hsw1); exact ⟨_, hd⟩
      · obtain ⟨dtWS, hdWS⟩ := (whiteSpaceSequence_iff hok hhtml).mpr ⟨by omega, by omega, hwAll⟩
        obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsHC rfl (.nt hneWSS hdWS rfl trivial hsw1); exact ⟨_, hd⟩
  intro k
  have hmain : ∀ (rem : Nat) (k : Nat), cs.size - k = rem →
      (∀ e, Lex.htmlClose Engine.builder cs k = some e →
        k + 3 ≤ e ∧ e ≤ cs.size ∧
        (∃ dt, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k e dt) ∧
        (∀ j dt, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k j dt → j ≤ e)) ∧
      (Lex.htmlClose Engine.builder cs k = none →
        ∀ j dt, ¬ (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k j dt) := by
    intro rem
    induction rem using Nat.strongRecOn with
    | ind rem ih =>
      intro k hrem
      let w := Lex.wsEnd Engine.builder cs k
      have ⟨hkw, _, _, _⟩ := wsEnd_spec cs k
      change k ≤ w at hkw
      constructor
      · intro e hhc
        unfold Lex.htmlClose at hhc
        dsimp only at hhc
        rw [show Lex.wsEnd Engine.builder cs k = w from rfl] at hhc
        rcases opt_none_or_some cs[w]? with hnw0 | ⟨cw0, hcw0⟩
        · rw [hnw0] at hhc; cases hhc
        · rw [hcw0] at hhc
          by_cases h2d : cw0 = 0x2D
          · subst h2d
            rcases opt_none_or_some cs[w + 1]? with hnw1 | ⟨cw1, hcw1⟩
            · rw [hnw1] at hhc; cases hhc
            · rw [hcw1] at hhc
              by_cases h2d1 : cw1 = 0x2D
              · subst h2d1
                rcases opt_none_or_some cs[w + 2]? with hnw2 | ⟨cw2, hcw2⟩
                · rw [hnw2] at hhc; cases hhc
                · rw [hcw2] at hhc
                  by_cases h3e : cw2 = 0x3E
                  · subst h3e
                    injection hhc with heEq; subst heEq
                    have hw3Sz : w + 3 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hcw2).1; omega
                    have ⟨_, hleSz, _, _⟩ := lineEnd_spec cs (w + 3)
                    have hw3Le : w + 3 ≤ Lex.lineEnd cs (w + 3) := lineEnd_ge_of_le cs hw3Sz
                    refine ⟨by omega, hleSz, hpackArrow hcw0 hcw1 hcw2, fun j dt hdj => ?_⟩
                    rcases hunpack hdj with ⟨_, _, _, _, hjLe⟩ | ⟨hg2f, _⟩
                    · exact hjLe
                    · rw [hcw0] at hg2f; cases hg2f
                  · simp [h3e] at hhc
              · simp [h2d1] at hhc
          · by_cases h2f : cw0 = 0x2F
            · subst h2f
              rcases opt_none_or_some cs[w + 1]? with hnw1 | ⟨cw1, hcw1⟩
              · rw [hnw1] at hhc; cases hhc
              · rw [hcw1] at hhc
                by_cases h2a : cw1 = 0x2A
                · subst h2a
                  rcases opt_none_or_some (Lex.closeAt cs (w + 2)) with hncl | ⟨c, hcl⟩
                  · rw [hncl] at hhc; cases hhc
                  · rw [hcl] at hhc; dsimp only at hhc
                    by_cases hanyLt : (cs.extract (w + 2) c).any Lex.isLT = true
                    · rw [hanyLt] at hhc; simp at hhc
                    · have hanyF : (cs.extract (w + 2) c).any Lex.isLT = false := Bool.eq_false_iff.mpr hanyLt
                      rw [hanyF] at hhc
                      simp only [Bool.false_eq_true, ↓reduceIte] at hhc
                      by_cases hcond : k < c + 2 ∧ c + 2 ≤ cs.size
                      · simp only [hcond, and_self, ↓reduceDIte] at hhc
                        have ⟨ihSome, _⟩ := ih (cs.size - (c + 2)) (by omega) (c + 2) rfl
                        obtain ⟨hc2e, heSz, ⟨dtSub, hdSub⟩, hubSub⟩ := ihSome e hhc
                        refine ⟨by omega, heSz, hpackDelim hcw0 hcw1 hcl hanyF hdSub, fun j dt hdj => ?_⟩
                        rcases hunpack hdj with ⟨hg2d, _⟩ | ⟨_, _, c', dt', hcl', _, _, _, hd'⟩
                        · rw [hcw0] at hg2d; cases hg2d
                        · have hceq : c' = c := Option.some.inj (hcl'.symm.trans hcl)
                          subst hceq; exact hubSub j dt' hd'
                      · simp only [hcond, ↓reduceDIte] at hhc; cases hhc
                · simp [h2a] at hhc
            · simp [h2d, h2f] at hhc
      · intro hhc j dt hdj
        unfold Lex.htmlClose at hhc
        dsimp only at hhc
        rcases hunpack hdj with ⟨hg0, hg1, hg2, _⟩ | ⟨hg0, hg1, c, dt', hcl, hanyF, hkc2, hc2Sz, hd'⟩
        · rw [hg0, hg1, hg2] at hhc; cases hhc
        · rw [hg0, hg1] at hhc
          rw [hcl] at hhc; dsimp only at hhc
          simp only [hanyF, Bool.false_eq_true, ↓reduceIte, hkc2, hc2Sz, and_self, ↓reduceDIte] at hhc
          exact (ih (cs.size - (c + 2)) (by omega) (c + 2) rfl).2 hhc j dt' hd'
  exact hmain (cs.size - k) k rfl

theorem htmlClose_no_isLT (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (hhtml : Lex.html cx = true) :
    ∀ {k j : Nat} {dt : DTree},
      (lexSpec cs cx).PlainDerives .HTMLCloseComment [] k j dt →
      ∀ p, k ≤ p → p < j → ∃ ch, cs[p]? = some ch ∧ Lex.isLT ch = false := by
  have haltsHC : Ecma.Spec.gl.alts cx .lexical .HTMLCloseComment = srcsOf .annexB Gen.AnnexB.HTMLCloseComment := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.1
  have haltsSeq : Ecma.Spec.gl.alts cx .lexical .SingleLineDelimitedCommentSequence =
      srcsOf .annexB Gen.AnnexB.SingleLineDelimitedCommentSequence := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.2.2.2.2.2.2.2.2.2
  have hseqNoLt : ∀ (sz : Nat) {a b : Nat} {dt : DTree}, sizeOf dt ≤ sz →
      (lexSpec cs cx).PlainDerives .SingleLineDelimitedCommentSequence [] a b dt →
      a < b ∧ ∀ p, a ≤ p → p < b → ∃ ch, cs[p]? = some ch ∧ Lex.isLT ch = false := by
    intro sz
    induction sz using Nat.strongRecOn with
    | ind sz ih =>
      intro a b dt hsz hd
      cases hd with
      | node ss hss _ _ _ hswS =>
        have hss := lex_mem_alts hok hss
        rw [haltsSeq] at hss
        simp [srcsOf, writtenAlts, Gen.AnnexB.SingleLineDelimitedCommentSequence] at hss; subst hss
        cases hswS with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdD _ _ hr1 =>
          obtain ⟨hg0, hg1, c, hcl, hnoLt, rfl⟩ := (singleLineDelimitedComment_iff hok hcp hhtml).mp ⟨_, hdD⟩
          obtain ⟨ha2c, hc1Sz, hc0, hc1, _⟩ := closeAt_some_spec cs (a + 2) c hcl
          have hdPart : ∀ p, a ≤ p → p < c + 2 → ∃ ch, cs[p]? = some ch ∧ Lex.isLT ch = false := by
            intro p hp1 hp2
            by_cases h0 : p = a
            · subst h0; exact ⟨0x2F, hg0, rfl⟩
            · by_cases h1 : p = a + 1
              · subst h1; exact ⟨0x2A, hg1, rfl⟩
              · by_cases h2 : p = c
                · subst h2; exact ⟨0x2A, hc0, rfl⟩
                · by_cases h3 : p = c + 1
                  · subst h3; exact ⟨0x2F, hc1, rfl⟩
                  · have hpGet : cs[p]? = some (cs[p]'(by omega)) := Array.getElem?_eq_getElem (by omega)
                    refine ⟨_, hpGet, ?_⟩
                    cases hl : Lex.isLT (cs[p]'(by omega)) with
                    | false => rfl
                    | true =>
                      have hexT := (extract_any_isLT_iff cs (a := a + 2) (by omega : c ≤ cs.size)).mpr
                        ⟨p, cs[p]'(by omega), by omega, by omega, hpGet, hl⟩
                      rw [hnoLt] at hexT; cases hexT
          rcases unpack_seq_opt_nt hr1 with ⟨_, _, hr2⟩ | ⟨hMid, _, _, _, _, htsEq, hdW, hr2⟩
          · cases hr2 with
            | absent hnil => cases hnil; exact ⟨by omega, hdPart⟩
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hdS2 _ _ hnil =>
              cases hnil
              obtain ⟨hlt2, hall2⟩ := ih (sz - 1)
                (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega)
                (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega) hdS2
              exact ⟨by omega, fun p hp1 hp2 => if hp : p < c + 2 then hdPart p hp1 hp else hall2 p (by omega) hp2⟩
          · subst htsEq
            obtain ⟨hltW, _, hallW⟩ := (whiteSpaceSequence_iff hok hhtml).mp ⟨_, hdW⟩
            have hwPart : ∀ p, c + 2 ≤ p → p < hMid → ∃ ch, cs[p]? = some ch ∧ Lex.isLT ch = false := by
              intro p hp1 hp2
              obtain ⟨ch, hch, hws⟩ := hallW p hp1 hp2
              exact ⟨ch, hch, isWS_not_isLT hws⟩
            cases hr2 with
            | absent hnil =>
              cases hnil
              exact ⟨by omega, fun p hp1 hp2 => if hp : p < c + 2 then hdPart p hp1 hp else hwPart p (by omega) hp2⟩
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hdS2 _ _ hnil =>
              cases hnil
              obtain ⟨hlt2, hall2⟩ := ih (sz - 1)
                (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega)
                (by simp +arith only [DTree.node.sizeOf_spec, List.cons.sizeOf_spec] at hsz; omega) hdS2
              refine ⟨by omega, fun p hp1 hp2 => ?_⟩
              by_cases hp : p < c + 2
              · exact hdPart p hp1 hp
              · by_cases hpW : p < hMid
                · exact hwPart p (by omega) hpW
                · exact hall2 p (by omega) hp2
  intro k j dt hd
  let sHC : Src := ⟨.annexB, Gen.AnnexB.HTMLCloseComment, 0,
    ⟨[], [.sym (.nt .WhiteSpaceSequence []) true, .sym (.nt .SingleLineDelimitedCommentSequence []) true,
          .sym (.t (.text "-->" false)) false, .sym (.nt .SingleLineCommentChars []) true], none⟩⟩
  cases hd with
  | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [haltsHC] at hs
    have hsEq : s = sHC := by simp [srcsOf, writtenAlts, Gen.AnnexB.HTMLCloseComment] at hs; exact hs
    subst hsEq
    have hr1NoLt : ∀ {w0 : Nat} {m1 : List Bool} {ts1 : List DTree},
        k ≤ w0 → (∀ p, k ≤ p → p < w0 → ∃ ch, cs[p]? = some ch ∧ Lex.isLT ch = false) →
        (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sHC [] 1
          [.sym (.nt .SingleLineDelimitedCommentSequence []) true,
           .sym (.t (.text "-->" false)) false,
           .sym (.nt .SingleLineCommentChars []) true] w0 j m1 ts1 →
        ∀ p, k ≤ p → p < j → ∃ ch, cs[p]? = some ch ∧ Lex.isLT ch = false := by
      intro w0 m1 ts1 hkw0 hwPart hr1
      have hr2NoLt : ∀ {w1 : Nat} {m2 : List Bool} {ts2 : List DTree},
          w0 ≤ w1 → (∀ p, k ≤ p → p < w1 → ∃ ch, cs[p]? = some ch ∧ Lex.isLT ch = false) →
          (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sHC [] 2
            [.sym (.t (.text "-->" false)) false, .sym (.nt .SingleLineCommentChars []) true] w1 j m2 ts2 →
          ∀ p, k ≤ p → p < j → ∃ ch, cs[p]? = some ch ∧ Lex.isLT ch = false := by
        intro w1 m2 ts2 hw01 hpre hr2
        cases hr2 with
        | term htArrow hr3 =>
          have hw3 : "-->".toList.map Char.toNat = [0x2D, 0x2D, 0x3E] := rfl
          obtain ⟨hmidEq, hg0, hg1f⟩ := termEnd_text_cons hw3 htArrow
          have hg1 := hg1f 0x2D [0x3E] rfl
          have hg2 : cs[w1 + 2]? = some 0x3E := by
            replace htArrow := lexTerm_eq htArrow
            unfold Code.termEnd at htArrow; dsimp only at htArrow; rw [hw3] at htArrow
            by_cases hc : (0 < ([0x2D, 0x2D, 0x3E] : List Nat).length && w1 + 3 ≤ cs.size &&
                (cs.extract w1 (w1 + 3)).toList == [0x2D, 0x2D, 0x3E]) = true
            · simp only [Bool.and_eq_true, beq_iff_eq] at hc
              have hex := hc.2; rw [extract_toList_eq_slice] at hex
              have hsc : (slice cs.toList w1 (w1 + 3))[2]? = some 0x3E := by rw [hex]; rfl
              unfold slice at hsc
              rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at hsc
              simpa using hsc
            · simp only [List.length_cons, List.length_nil] at htArrow hc
              simp only [hc, Bool.false_eq_true, ↓reduceIte] at htArrow; cases htArrow
          simp at hmidEq; subst hmidEq
          have harrowPart : ∀ p, k ≤ p → p < w1 + 3 → ∃ ch, cs[p]? = some ch ∧ Lex.isLT ch = false := by
            intro p hp1 hp2
            by_cases hp : p < w1
            · exact hpre p hp1 hp
            · by_cases hp0 : p = w1
              · subst hp0; exact ⟨0x2D, hg0, rfl⟩
              · by_cases hp1' : p = w1 + 1
                · subst hp1'; exact ⟨0x2D, hg1, rfl⟩
                · have hp2' : p = w1 + 2 := by omega
                  subst hp2'; exact ⟨0x3E, hg2, rfl⟩
          cases hr3 with
          | absent hnil => cases hnil; exact harrowPart
          | leaf _ hl _ _ _ => exact nomatch hl
          | nt _ hdSLC _ _ hnil =>
            cases hnil
            obtain ⟨_, _, hallSLC⟩ := (singleLineCommentChars_iff hok hcp).mp ⟨_, hdSLC⟩
            exact fun p hp1 hp2 => if hp : p < w1 + 3 then harrowPart p hp1 hp else hallSLC p (by omega) hp2
      cases hr1 with
      | absent hr2 => exact hr2NoLt (Nat.le_refl _) hwPart hr2
      | leaf _ hl _ _ _ => exact nomatch hl
      | nt _ hdSeq _ _ hr2 =>
        obtain ⟨hltS, hallS⟩ := hseqNoLt (sizeOf _) (Nat.le_refl _) hdSeq
        exact hr2NoLt (Nat.le_of_lt hltS)
          (fun p hp1 hp2 => if hp : p < w0 then hwPart p hp1 hp else hallS p (by omega) hp2) hr2
    cases hsw with
    | absent hr1 => exact hr1NoLt (Nat.le_refl _) (fun _ h1 h2 => by omega) hr1
    | leaf _ hl _ _ _ => exact nomatch hl
    | nt _ hdWS _ _ hr1 =>
      obtain ⟨hltW, _, hallW⟩ := (whiteSpaceSequence_iff hok hhtml).mp ⟨_, hdWS⟩
      exact hr1NoLt (Nat.le_of_lt hltW)
        (fun p hp1 hp2 => let ⟨ch, hch, hws⟩ := hallW p hp1 hp2; ⟨ch, hch, isWS_not_isLT hws⟩) hr1

/-! ## `Comment` (`MultiLineComment` + Annex B `Comment`) -/

theorem annexBMultiLine_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (hhtml : Lex.html cx = true) {i j : Nat} :
    let sAnnex : Src := ⟨.annexB, Gen.AnnexB.MultiLineComment, 0,
      ⟨[], [.sym (.t (.text "/*" false)) false, .sym (.nt .FirstCommentLine []) true,
            .sym (.nt .LineTerminator []) false, .sym (.nt .MultiLineCommentChars []) true,
            .sym (.t (.text "*/" false)) false, .sym (.nt .HTMLCloseComment []) true], none⟩⟩
    (∃ m kids, (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sAnnex [] 0 sAnnex.alt.rhs i j m kids) ↔
      (cs[i]? = some 0x2F ∧ cs[i + 1]? = some 0x2A ∧
       ∃ c, Lex.closeAt cs (i + 2) = some c ∧ (cs.extract (i + 2) c).any Lex.isLT = true ∧
         (j = c + 2 ∨ ∃ dtHC, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] (c + 2) j dtHC)) := by
  intro sAnnex
  have haltsFC : Ecma.Spec.gl.alts cx .lexical .FirstCommentLine = srcsOf .annexB Gen.AnnexB.FirstCommentLine := by
    rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte]; exact alts_cert_annexB.2.2.1
  let sFC : Src := ⟨.annexB, Gen.AnnexB.FirstCommentLine, 0,
    ⟨[], [.sym (.nt .SingleLineDelimitedCommentChars []) false], none⟩⟩
  have hsFC : sFC ∈ Ecma.Spec.gl.alts cx .lexical .FirstCommentLine := by rw [haltsFC]; exact mem_of_get? 0 rfl
  have hneFC : (altsOf cx .lexical .FirstCommentLine).isEmpty = false := altsOf_nonempty_of_mem hok hsFC
  have hneSLDC : (altsOf cx .lexical .SingleLineDelimitedCommentChars).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_html_true_eq hhtml alts_cert_annexB.2.2.2.2.2.2.1) rfl
  have hneLT : (altsOf cx .lexical .LineTerminator).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.2.2.2.2.1 alts_cert_trivia.2.2.2.2.2.1) rfl
  have hneMLC : (altsOf cx .lexical .MultiLineCommentChars).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.1 alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
  have hneHC : (altsOf cx .lexical .HTMLCloseComment).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_html_true_eq hhtml alts_cert_annexB.2.1) rfl
  constructor
  · rintro ⟨_, _, hsw0⟩; cases hsw0 with | term htO hr1 =>
    obtain ⟨hmidO, hg0, hg1f⟩ := termEnd_text_cons (c0 := 0x2F) (csRest := [0x2A]) rfl htO
    have hg1 := hg1f 0x2A [] rfl
    simp at hmidO; subst hmidO
    have hafterFC : ∀ {ltPos : Nat} {m2 : List Bool} {ts2 : List DTree},
        (ltPos = i + 2 ∨ (i + 2 < ltPos ∧ ∃ dtSL, (lexSpec cs cx).PlainDerives .SingleLineDelimitedCommentChars [] (i + 2) ltPos dtSL)) →
        (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sAnnex [] 2
          [.sym (.nt .LineTerminator []) false, .sym (.nt .MultiLineCommentChars []) true,
           .sym (.t (.text "*/" false)) false, .sym (.nt .HTMLCloseComment []) true] ltPos j m2 ts2 →
        ∃ c, Lex.closeAt cs (i + 2) = some c ∧ (cs.extract (i + 2) c).any Lex.isLT = true ∧
          (j = c + 2 ∨ ∃ dtHC, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] (c + 2) j dtHC) := by
      intro ltPos m2 ts2 hfc hr2
      cases hr2 with
      | leaf _ hl _ _ _ => exact nomatch hl
      | nt _ hdLT _ _ hr3 =>
        obtain ⟨clt, hcltGet, hcltIs, rfl⟩ := (lineTerminator_iff hok).mp ⟨_, hdLT⟩
        have hltPosSz : ltPos < cs.size := (Array.getElem?_eq_some_iff.mp hcltGet).1
        have hltNot2f : cs[ltPos]? ≠ some 0x2F := by
          intro h2f; rw [hcltGet] at h2f; injection h2f with he; subst he; cases hcltIs
        have hltNot2a : cs[ltPos]? ≠ some 0x2A := by
          intro h2a; rw [hcltGet] at h2a; injection h2a with he; subst he; cases hcltIs
        have hnoCloseFC : i + 2 ≤ ltPos ∧ ∀ q, i + 2 ≤ q → q < ltPos → ¬(cs[q]? = some 0x2A ∧ cs[q + 1]? = some 0x2F) := by
          rcases hfc with rfl | ⟨hlt, dtSL, hdSL⟩
          · exact ⟨Nat.le_refl _, fun _ h1 h2 => by omega⟩
          · have hall := (slDelimChars_iff hok hcp hhtml (Nat.le_of_lt hltPosSz) hltNot2f (ltPos - (i + 2)) rfl hlt).1.mp ⟨_, hdSL⟩
            exact ⟨Nat.le_of_lt hlt, fun q hq1 hq2 => (hall q hq1 hq2).2⟩
        have hafterMLC : ∀ {c : Nat} {m4 : List Bool} {ts4 : List DTree},
            (c = ltPos + 1 ∨ (ltPos + 1 < c ∧ ∃ dtM, (lexSpec cs cx).PlainDerives .MultiLineCommentChars [] (ltPos + 1) c dtM)) →
            (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sAnnex [] 4
              [.sym (.t (.text "*/" false)) false, .sym (.nt .HTMLCloseComment []) true] c j m4 ts4 →
            ∃ c0, Lex.closeAt cs (i + 2) = some c0 ∧ (cs.extract (i + 2) c0).any Lex.isLT = true ∧
              (j = c0 + 2 ∨ ∃ dtHC, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] (c0 + 2) j dtHC) := by
          intro c m4 ts4 hmlc hr4
          cases hr4 with
          | term htC hr5 =>
            obtain ⟨hmidC, hc0, hc1f⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := [0x2F]) rfl htC
            have hc1 := hc1f 0x2F [] rfl
            simp at hmidC; subst hmidC
            have hcSz : c ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hc0).1; omega
            have hcNot2f : cs[c]? ≠ some 0x2F := by rw [hc0]; decide
            have hnoCloseAll : ltPos + 1 ≤ c ∧ ∀ q, i + 2 ≤ q → q < c → ¬(cs[q]? = some 0x2A ∧ cs[q + 1]? = some 0x2F) := by
              rcases hmlc with rfl | ⟨hltM, dtM, hdM⟩
              · refine ⟨Nat.le_refl _, fun q hq1 hq2 => ?_⟩
                by_cases hqlt : q < ltPos
                · exact hnoCloseFC.2 q hq1 hqlt
                · have : q = ltPos := by omega
                  subst this; exact fun ⟨ha, _⟩ => hltNot2a ha
              · have hallM := (multiLineChars_iff hok hcp hcSz hcNot2f (c - (ltPos + 1)) rfl hltM).1.mp ⟨_, hdM⟩
                refine ⟨Nat.le_of_lt hltM, fun q hq1 hq2 => ?_⟩
                by_cases hqlt : q < ltPos
                · exact hnoCloseFC.2 q hq1 hqlt
                · by_cases hqeq : q = ltPos
                  · subst hqeq; exact fun ⟨ha, _⟩ => hltNot2a ha
                  · exact hallM q (by omega) hq2
            have hcl := closeAt_eq_some_of_no_earlier (by omega) hc0 hc1 hnoCloseAll.2
            have hanyLt : (cs.extract (i + 2) c).any Lex.isLT = true :=
              (extract_any_isLT_iff cs hcSz).mpr ⟨ltPos, clt, hnoCloseFC.1, by omega, hcltGet, hcltIs⟩
            cases hr5 with
            | absent hnil => cases hnil; exact ⟨c, hcl, hanyLt, Or.inl rfl⟩
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hdHC _ _ hnil => cases hnil; exact ⟨c, hcl, hanyLt, Or.inr ⟨_, hdHC⟩⟩
        cases hr3 with
        | absent hr4 => exact hafterMLC (Or.inl rfl) hr4
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdM _ _ hr4 =>
          exact hafterMLC (Or.inr ⟨multiLineChars_pos hok hcp hdM, _, hdM⟩) hr4
    refine ⟨hg0, hg1, ?_⟩
    cases hr1 with
    | absent hr2 => exact hafterFC (Or.inl rfl) hr2
    | leaf _ hl _ _ _ => exact nomatch hl
    | nt _ hdFC _ _ hr2 =>
      cases hdFC with
      | node sfc hsfc _ _ _ hswFC =>
        have hsfc := lex_mem_alts hok hsfc
        rw [haltsFC] at hsfc
        simp [srcsOf, writtenAlts, Gen.AnnexB.FirstCommentLine] at hsfc; subst hsfc
        cases hswFC with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdSL _ _ hnilFC =>
          cases hnilFC
          exact hafterFC (Or.inr ⟨slDelimChars_pos hok hcp hhtml hdSL, _, hdSL⟩) hr2
  · rintro ⟨hg0, hg1, c, hcl, hanyLt, hjChoice⟩
    obtain ⟨hi2c, hc1Sz, hc0, hc1, hnoEarlier⟩ := closeAt_some_spec cs (i + 2) c hcl
    obtain ⟨hi2Sz, hexO⟩ := extract_two_eq hg0 hg1
    obtain ⟨hc2Sz, hexC⟩ := extract_two_eq hc0 hc1
    have htO := termEnd_text_mk "/*" false i (by decide) hi2Sz hexO
    have htC := termEnd_text_mk "*/" false c (by decide) hc2Sz hexC
    let ltPos := Lex.lineEnd cs (i + 2)
    have ⟨_, hleSz, hleNo, hleAt⟩ := lineEnd_spec cs (i + 2)
    have hi2LeLt : i + 2 ≤ ltPos := lineEnd_ge_of_le cs hi2Sz
    obtain ⟨pLt, cLt, hpLt1, hpLt2, hpLtGet, hpLtIs⟩ := (extract_any_isLT_iff cs (by omega)).mp hanyLt
    have hltPosLtC : ltPos < c := by
      apply Classical.byContradiction; intro hge
      obtain ⟨ch', hch', hnlt'⟩ := hleNo pLt hpLt1 (by omega)
      rw [hpLtGet] at hch'; injection hch' with he; subst he; rw [hpLtIs] at hnlt'; cases hnlt'
    obtain ⟨clt0, hcltGet, hcltIs⟩ := hleAt (by omega)
    obtain ⟨dtLT, hdLT⟩ := (lineTerminator_iff hok).mpr ⟨clt0, hcltGet, hcltIs, rfl⟩
    have hsw5 : ∃ m5 ts5, (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sAnnex [] 5
        [.sym (.nt .HTMLCloseComment []) true] (c + 2) j m5 ts5 := by
      rcases hjChoice with rfl | ⟨dtHC, hdHC⟩
      · exact ⟨_, _, .absent .nil⟩
      · exact ⟨_, _, .nt hneHC hdHC rfl trivial .nil⟩
    obtain ⟨_, _, hr5⟩ := hsw5
    have hsw3 : ∃ m3 ts3, (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sAnnex [] 3
        [.sym (.nt .MultiLineCommentChars []) true, .sym (.t (.text "*/" false)) false,
         .sym (.nt .HTMLCloseComment []) true] (ltPos + 1) j m3 ts3 := by
      by_cases hlt1Eq : ltPos + 1 = c
      · subst hlt1Eq; exact ⟨_, _, .absent (.term htC hr5)⟩
      · have hcNot2f : cs[c]? ≠ some 0x2F := by rw [hc0]; decide
        obtain ⟨dtM, hdM⟩ := (multiLineChars_iff hok hcp (by omega) hcNot2f (c - (ltPos + 1)) rfl (by omega)).1.mpr
          (fun q hq1 hq2 => hnoEarlier q (by omega) hq2)
        exact ⟨_, _, .nt hneMLC hdM rfl trivial (.term htC hr5)⟩
    obtain ⟨_, _, hr3⟩ := hsw3
    by_cases hfcEq : i + 2 = ltPos
    · have htO' : Code.termEnd Engine.builder cs (.text "/*" false) i = some ltPos := by
        rw [← hfcEq]; exact htO
      exact ⟨_, _, .term htO' (.absent (.nt hneLT hdLT rfl trivial hr3))⟩
    · have hltNot2f : cs[ltPos]? ≠ some 0x2F := by
        intro h2f; rw [hcltGet] at h2f; injection h2f with he; subst he; cases hcltIs
      obtain ⟨dtSL, hdSL⟩ := (slDelimChars_iff hok hcp hhtml (by omega) hltNot2f (ltPos - (i + 2)) rfl (by omega)).1.mpr
        (fun q hq1 hq2 => ⟨hleNo q hq1 hq2, hnoEarlier q hq1 (by omega)⟩)
      obtain ⟨_, hdFC⟩ := mkLexPlainSimple hok hsFC rfl (.nt hneSLDC hdSL rfl trivial .nil)
      exact ⟨_, _, .term htO (.nt hneFC hdFC rfl trivial (.nt hneLT hdLT rfl trivial hr3))⟩

theorem mainMultiLine_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {i j : Nat} :
    let sMain : Src := ⟨.lexical, Gen.Lexical.MultiLineComment, 0,
      ⟨[], [.sym (.t (.text "/*" false)) false, .sym (.nt .MultiLineCommentChars []) true, .sym (.t (.text "*/" false)) false], none⟩⟩
    (∃ m kids, (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sMain [] 0 sMain.alt.rhs i j m kids) ↔
      (cs[i]? = some 0x2F ∧ cs[i + 1]? = some 0x2A ∧ ∃ c, Lex.closeAt cs (i + 2) = some c ∧ j = c + 2) := by
  intro sMain
  have hneMLC : (altsOf cx .lexical .MultiLineCommentChars).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.1 alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
  constructor
  · rintro ⟨_, _, hsw0⟩; cases hsw0 with | term htO hr1 =>
    obtain ⟨hmidO, hg0, hg1f⟩ := termEnd_text_cons (c0 := 0x2F) (csRest := [0x2A]) rfl htO
    have hg1 := hg1f 0x2A [] rfl
    simp at hmidO; subst hmidO
    rcases unpack_seq_opt_nt hr1 with ⟨_, _, hr2⟩ | ⟨cEnd, _, _, _, _, _, hdM, hr2⟩
    · cases hr2 with
      | term htC hnil =>
        cases hnil
        obtain ⟨hjEq, hc0, hc1f⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := [0x2F]) rfl htC
        have hc1 := hc1f 0x2F [] rfl
        simp at hjEq
        exact ⟨hg0, hg1, i + 2, closeAt_eq_some_of_no_earlier (Nat.le_refl _) hc0 hc1 (fun _ h1 h2 => by omega), by omega⟩
    · cases hr2 with
      | term htC hnil =>
        cases hnil
        obtain ⟨hjEq, hc0, hc1f⟩ := termEnd_text_cons (c0 := 0x2A) (csRest := [0x2F]) rfl htC
        have hc1 := hc1f 0x2F [] rfl
        simp at hjEq
        have hcSz : cEnd ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hc0).1; omega
        have hcNot2f : cs[cEnd]? ≠ some 0x2F := by rw [hc0]; decide
        have hpLt := multiLineChars_pos hok hcp hdM
        have hall := (multiLineChars_iff hok hcp hcSz hcNot2f (cEnd - (i + 2)) rfl hpLt).1.mp ⟨_, hdM⟩
        exact ⟨hg0, hg1, cEnd, closeAt_eq_some_of_no_earlier (Nat.le_of_lt hpLt) hc0 hc1 hall, by omega⟩
  · rintro ⟨hg0, hg1, c, hcl, rfl⟩
    obtain ⟨hi2c, _, hc0, hc1, hnoEarlier⟩ := closeAt_some_spec cs (i + 2) c hcl
    obtain ⟨hi2Sz, hexO⟩ := extract_two_eq hg0 hg1
    obtain ⟨hc2Sz, hexC⟩ := extract_two_eq hc0 hc1
    have htO := termEnd_text_mk "/*" false i (by decide) hi2Sz hexO
    have htC := termEnd_text_mk "*/" false c (by decide) hc2Sz hexC
    by_cases hce : c = i + 2
    · subst hce; exact ⟨_, _, .term htO (.absent (.term htC .nil))⟩
    · have hcNot2f : cs[c]? ≠ some 0x2F := by rw [hc0]; decide
      obtain ⟨dtM, hdM⟩ := (multiLineChars_iff hok hcp (by omega) hcNot2f (c - (i + 2)) rfl (by omega)).1.mpr hnoEarlier
      exact ⟨_, _, .term htO (.nt hneMLC hdM rfl trivial (.term htC .nil))⟩

theorem comment_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {i j : Nat} :
    (∃ dt, (lexSpec cs cx).PlainDerives .Comment [] i j dt) ↔
      ((cs[i]? = some 0x2F ∧ cs[i + 1]? = some 0x2F ∧ i + 2 ≤ j ∧ j ≤ Lex.lineEnd cs (i + 2)) ∨
       (cs[i]? = some 0x2F ∧ cs[i + 1]? = some 0x2A ∧ ∃ c, Lex.closeAt cs (i + 2) = some c ∧
          (j = c + 2 ∨ (Lex.html cx = true ∧ (cs.extract (i + 2) c).any Lex.isLT = true ∧
            ∃ dtHC, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] (c + 2) j dtHC))) ∨
       (Lex.html cx = true ∧ cs[i]? = some 0x3C ∧ cs[i + 1]? = some 0x21 ∧ cs[i + 2]? = some 0x2D ∧ cs[i + 3]? = some 0x2D ∧
          i + 4 ≤ j ∧ j ≤ Lex.lineEnd cs (i + 4)) ∨
       (Lex.html cx = true ∧ ∃ c, cs[i]? = some c ∧ Lex.isLT c = true ∧
          ∃ dtHC, (lexSpec cs cx).PlainDerives .HTMLCloseComment []
            (if c == 0xD && cs[i + 1]? == some 0xA then i + 2 else i + 1) j dtHC)) := by
  let sC0 : Src := ⟨.lexical, Gen.Lexical.Comment, 0, ⟨[], [.sym (.nt .MultiLineComment []) false], none⟩⟩
  let sC1 : Src := ⟨.lexical, Gen.Lexical.Comment, 1, ⟨[], [.sym (.nt .SingleLineComment []) false], none⟩⟩
  have hsC0 : sC0 ∈ Ecma.Spec.gl.alts cx .lexical .Comment := by
    cases h : Lex.html cx with
    | false => exact mem_alts_of_get? (alts_html_false_eq h alts_cert_trivia.2.2.2.2.2.2.2.2.1) 0 rfl
    | true => exact mem_alts_of_get? (alts_html_true_eq h alts_cert_trivia.2.2.2.2.2.2.2.2.2.1) 0 rfl
  have hsC1 : sC1 ∈ Ecma.Spec.gl.alts cx .lexical .Comment := by
    cases h : Lex.html cx with
    | false => exact mem_alts_of_get? (alts_html_false_eq h alts_cert_trivia.2.2.2.2.2.2.2.2.1) 1 rfl
    | true => exact mem_alts_of_get? (alts_html_true_eq h alts_cert_trivia.2.2.2.2.2.2.2.2.2.1) 1 rfl
  let sML0 : Src := ⟨.lexical, Gen.Lexical.MultiLineComment, 0,
    ⟨[], [.sym (.t (.text "/*" false)) false, .sym (.nt .MultiLineCommentChars []) true, .sym (.t (.text "*/" false)) false], none⟩⟩
  have hsML0 : sML0 ∈ Ecma.Spec.gl.alts cx .lexical .MultiLineComment := by
    cases h : Lex.html cx with
    | false => exact mem_alts_of_get? (alts_html_false_eq h alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.1) 0 rfl
    | true => exact mem_alts_of_get? (alts_html_true_eq h alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.1) 0 rfl
  have hneML : (altsOf cx .lexical .MultiLineComment).isEmpty = false := altsOf_nonempty_of_mem hok hsML0
  have hneSL : (altsOf cx .lexical .SingleLineComment).isEmpty = false :=
    altsOf_nonempty_of_srcs1 hok (alts_fixed_eq
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) rfl
  constructor
  · rintro ⟨_, hd0⟩; cases hd0 with | node s hs _ _ _ hsw =>
    have hs := lex_mem_alts hok hs
    rw [alts_lexical_eq] at hs
    cases hhtml : Lex.html cx with
    | false =>
      simp only [hhtml, Bool.false_eq_true, ↓reduceIte, alts_cert_trivia.2.2.2.2.2.2.2.2.1,
        srcsOf, writtenAlts, Gen.Lexical.Comment, List.zipIdx_cons, List.zipIdx_nil,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · cases hsw with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdML _ _ hnil =>
          cases hnil
          cases hdML with
          | node sml hsml _ _ _ hswML =>
            have hsml := lex_mem_alts hok hsml
            rw [alts_lexical_eq, hhtml] at hsml
            simp only [Bool.false_eq_true, ↓reduceIte, alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.1,
              srcsOf, writtenAlts, Gen.Lexical.MultiLineComment, List.zipIdx_cons, List.zipIdx_nil,
              List.map_cons, List.map_nil, List.mem_singleton] at hsml
            subst hsml
            obtain ⟨hg0, hg1, c, hcl, rfl⟩ := (mainMultiLine_iff hok hcp).mp ⟨_, _, hswML⟩
            exact Or.inr (Or.inl ⟨hg0, hg1, c, hcl, Or.inl rfl⟩)
      · cases hsw with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdSL _ _ hnil =>
          cases hnil
          exact Or.inl ((singleLineComment_iff hok hcp).mp ⟨_, hdSL⟩)
    | true =>
      simp only [hhtml, ↓reduceIte, alts_cert_trivia.2.2.2.2.2.2.2.2.2.1,
        srcsOf, writtenAlts, Gen.Lexical.Comment, Gen.AnnexB.Comment, List.zipIdx_cons, List.zipIdx_nil,
        List.map_cons, List.map_nil, List.drop, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · cases hsw with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdML _ _ hnil =>
          cases hnil
          cases hdML with
          | node sml hsml _ _ _ hswML =>
            have hsml := lex_mem_alts hok hsml
            rw [alts_lexical_eq, hhtml] at hsml
            simp only [↓reduceIte, alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.1,
              srcsOf, writtenAlts, Gen.Lexical.MultiLineComment, Gen.AnnexB.MultiLineComment,
              List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
              List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hsml
            rcases hsml with rfl | rfl
            · obtain ⟨hg0, hg1, c, hcl, rfl⟩ := (mainMultiLine_iff hok hcp).mp ⟨_, _, hswML⟩
              exact Or.inr (Or.inl ⟨hg0, hg1, c, hcl, Or.inl rfl⟩)
            · obtain ⟨hg0, hg1, c, hcl, hanyLt, hjC⟩ := (annexBMultiLine_iff hok hcp hhtml).mp ⟨_, _, hswML⟩
              rcases hjC with rfl | hhc
              · exact Or.inr (Or.inl ⟨hg0, hg1, c, hcl, Or.inl rfl⟩)
              · exact Or.inr (Or.inl ⟨hg0, hg1, c, hcl, Or.inr ⟨rfl, hanyLt, hhc⟩⟩)
      · cases hsw with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdSL _ _ hnil =>
          cases hnil
          exact Or.inl ((singleLineComment_iff hok hcp).mp ⟨_, hdSL⟩)
      · cases hsw with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdHO _ _ hnil =>
          cases hnil
          obtain ⟨hg0, hg1, hg2, hg3, h1, h2⟩ := (singleLineHTMLOpenComment_iff hok hcp hhtml).mp ⟨_, hdHO⟩
          exact Or.inr (Or.inr (Or.inl ⟨rfl, hg0, hg1, hg2, hg3, h1, h2⟩))
      · cases hsw with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdHC _ _ hnil =>
          cases hnil
          cases hdHC with
          | node shc hshc _ _ _ hswHC =>
            have hshc := lex_mem_alts hok hshc
            rw [alts_lexical_eq, hhtml] at hshc
            simp only [↓reduceIte, alts_cert_annexB.2.2.2.2.1,
              srcsOf, writtenAlts, Gen.AnnexB.SingleLineHTMLCloseComment,
              List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_singleton] at hshc
            subst hshc
            cases hswHC with
            | leaf _ hl _ _ _ => exact nomatch hl
            | nt _ hdLTS _ _ hrHC =>
              cases hrHC with
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdClose _ _ hnil2 =>
                cases hnil2
                obtain ⟨c, hc, hlt, rfl⟩ := (lineTerminatorSequence_iff hok).mp ⟨_, hdLTS⟩
                exact Or.inr (Or.inr (Or.inr ⟨rfl, c, hc, hlt, _, hdClose⟩))
      · cases hsw with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdSLD _ _ hnil =>
          cases hnil
          obtain ⟨hg0, hg1, c, hcl, _, rfl⟩ := (singleLineDelimitedComment_iff hok hcp hhtml).mp ⟨_, hdSLD⟩
          exact Or.inr (Or.inl ⟨hg0, hg1, c, hcl, Or.inl rfl⟩)
  · rintro (hsl | ⟨hg0, hg1, c, hcl, hml⟩ | ⟨hhtml, hg0, hg1, hg2, hg3, h1, h2⟩ | ⟨hhtml, c, hc, hlt, dtHC, hdHC⟩)
    · obtain ⟨dtSL, hdSL⟩ := (singleLineComment_iff hok hcp).mpr hsl
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsC1 rfl (.nt hneSL hdSL rfl trivial .nil); exact ⟨_, hd⟩
    · rcases hml with rfl | ⟨hhtml, hanyLt, dtHC, hdHC⟩
      · obtain ⟨_, _, hswML⟩ := (mainMultiLine_iff hok hcp).mpr ⟨hg0, hg1, c, hcl, rfl⟩
        obtain ⟨_, hdML⟩ := mkLexPlainSimple hok hsML0 rfl hswML
        obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsC0 rfl (.nt hneML hdML rfl trivial .nil); exact ⟨_, hd⟩
      · let sML1 : Src := ⟨.annexB, Gen.AnnexB.MultiLineComment, 0,
          ⟨[], [.sym (.t (.text "/*" false)) false, .sym (.nt .FirstCommentLine []) true,
                .sym (.nt .LineTerminator []) false, .sym (.nt .MultiLineCommentChars []) true,
                .sym (.t (.text "*/" false)) false, .sym (.nt .HTMLCloseComment []) true], none⟩⟩
        have hsML1 : sML1 ∈ Ecma.Spec.gl.alts cx .lexical .MultiLineComment := by
          rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte, alts_cert_trivia.2.2.2.2.2.2.2.2.2.2.2.1]
          exact mem_of_get? 1 rfl
        obtain ⟨_, _, hswML⟩ := (annexBMultiLine_iff hok hcp hhtml).mpr ⟨hg0, hg1, c, hcl, hanyLt, Or.inr ⟨dtHC, hdHC⟩⟩
        obtain ⟨_, hdML⟩ := mkLexPlainSimple hok hsML1 rfl hswML
        obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsC0 rfl (.nt hneML hdML rfl trivial .nil); exact ⟨_, hd⟩
    · let sC2 : Src := ⟨.annexB, Gen.AnnexB.Comment, 2, ⟨[], [.sym (.nt .SingleLineHTMLOpenComment []) false], none⟩⟩
      have hsC2 : sC2 ∈ Ecma.Spec.gl.alts cx .lexical .Comment := by
        rw [alts_lexical_eq, hhtml]; simp only [↓reduceIte, alts_cert_trivia.2.2.2.2.2.2.2.2.2.1]
        exact mem_of_get? 2 rfl
      have hneHO : (altsOf cx .lexical .SingleLineHTMLOpenComment).isEmpty = false :=
        altsOf_nonempty_of_srcs1 hok (alts_html_true_eq hhtml alts_cert_annexB.2.2.2.1) rfl
      obtain ⟨dtHO, hdHO⟩ := (singleLineHTMLOpenComment_iff hok hcp hhtml).mpr ⟨hg0, hg1, hg2, hg3, h1, h2⟩
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsC2 rfl (.nt hneHO hdHO rfl trivial .nil); exact ⟨_, hd⟩
    · let sC3 : Src := ⟨.annexB, Gen.AnnexB.Comment, 3, ⟨[], [.sym (.nt .SingleLineHTMLCloseComment []) false], none⟩⟩
      let sSHC : Src := ⟨.annexB, Gen.AnnexB.SingleLineHTMLCloseComment, 0,
        ⟨[], [.sym (.nt .LineTerminatorSequence []) false, .sym (.nt .HTMLCloseComment []) false], none⟩⟩
      have hsC3 : sC3 ∈ Ecma.Spec.gl.alts cx .lexical .Comment :=
        mem_alts_of_get? (alts_html_true_eq hhtml alts_cert_trivia.2.2.2.2.2.2.2.2.2.1) 3 rfl
      have hsSHC : sSHC ∈ Ecma.Spec.gl.alts cx .lexical .SingleLineHTMLCloseComment :=
        mem_alts_of_get? (alts_html_true_eq hhtml alts_cert_annexB.2.2.2.2.1) 0 rfl
      have hneSHC : (altsOf cx .lexical .SingleLineHTMLCloseComment).isEmpty = false := altsOf_nonempty_of_mem hok hsSHC
      have hneLTS : (altsOf cx .lexical .LineTerminatorSequence).isEmpty = false :=
        altsOf_nonempty_of_srcs1 hok (alts_fixed_eq alts_cert_trivia.2.2.2.2.2.2.1 alts_cert_trivia.2.2.2.2.2.2.2.1) rfl
      have hneHC : (altsOf cx .lexical .HTMLCloseComment).isEmpty = false :=
        altsOf_nonempty_of_srcs1 hok (alts_html_true_eq hhtml alts_cert_annexB.2.1) rfl
      obtain ⟨dtLTS, hdLTS⟩ := (lineTerminatorSequence_iff hok).mpr ⟨c, hc, hlt, rfl⟩
      obtain ⟨_, hdSHC⟩ := mkLexPlainSimple hok hsSHC rfl (.nt hneLTS hdLTS rfl trivial (.nt hneHC hdHC rfl trivial .nil))
      obtain ⟨_, hd⟩ := mkLexPlainSimple hok hsC3 rfl (.nt hneSHC hdSHC rfl trivial .nil); exact ⟨_, hd⟩


/-! ## Section 4: Lexical goals, `InputElement*` decomposition, `Trivia`/`skip`, follow rule, and `lexAtPure` -/

def isSynLexGoal (g : NT) : Bool :=
  g == .InputElementDiv || g == .InputElementRegExp || g == .InputElementTemplateTail

def isLexGoal (g : NT) : Bool :=
  g == .InputElementDiv || g == .InputElementRegExp ||
  g == .InputElementRegExpOrTemplateTail || g == .InputElementTemplateTail ||
  g == .InputElementHashbangOrRegExp

theorem isSynLexGoal_lexicalGoalOf (n : NT) : isSynLexGoal (lexicalGoalOf n) = true := by
  unfold lexicalGoalOf isSynLexGoal
  by_cases h1 : (n == .RegularExpressionLiteral) = true
  · simp [h1]
  · by_cases h2 : (n == .TemplateMiddle || n == .TemplateTail) = true <;> simp [h1, h2]

theorem isLexGoal_of_isSynLexGoal {g : NT} (h : isSynLexGoal g = true) : isLexGoal g = true := by
  unfold isSynLexGoal at h
  unfold isLexGoal
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inr h)

theorem classes_sub_allTokClasses (g : NT) : ∀ c ∈ Lex.classes g, c ∈ allTokClasses := by
  unfold Lex.classes
  split <;> decide

theorem classes_nodup (g : NT) : (Lex.classes g).Nodup := by
  unfold Lex.classes
  split <;> decide

/-! ### `Tree.has .NumericLiteral` characterization -/

private theorem tree_has_node (target m : NT) (id : Nat) (ps : List Param) (a b i j : Nat) (kids : List Tree) :
    (Tree.node m id ps a b kids).has target i j =
      ((m == target && a == i && b == j) || kids.any (Tree.has target i j)) := by
  unfold Tree.has
  congr 1
  induction kids with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.attach_cons, List.any_cons, List.any_map]
    congr 1

private def numLitAncNTs : List NT :=
  [.InputElementDiv, .InputElementRegExp, .InputElementRegExpOrTemplateTail,
   .InputElementTemplateTail, .InputElementHashbangOrRegExp, .CommonToken, .NumericLiteral]

private def rhsAvoidsAnc : List Item → Bool
  | [] => true
  | .sym (.nt m _) _ :: rest => !numLitAncNTs.contains m && rhsAvoidsAnc rest
  | .butNot (.nt m _) _ :: rest => !numLitAncNTs.contains m && rhsAvoidsAnc rest
  | _ :: rest => rhsAvoidsAnc rest

private def lexRulesAvoidCert : Bool :=
  (glData.rulesOf .lexical).all (fun r =>
    if !numLitAncNTs.contains r.lhs || r.lhs == .NumericLiteral then
      (writtenAlts r).all fun a => rhsAvoidsAnc a.rhs
    else true) &&
  glData.blocks.all (fun b =>
    match b.kind with
    | .overlay sec _ _ =>
      !(overlayGrammar sec == .lexical) ||
      b.rules.all (fun r =>
        if !numLitAncNTs.contains r.lhs || r.lhs == .NumericLiteral then
          (writtenAlts r).all fun a => rhsAvoidsAnc a.rhs
        else true)
    | _ => true)

private theorem lexRulesAvoidCert_true : lexRulesAvoidCert = true := by decide

private theorem lex_alt_rhsAvoidsAnc {cx : Ctx} {n : NT} {s : Src}
    (hs : s ∈ Ecma.Spec.gl.alts cx .lexical n)
    (hn : (!numLitAncNTs.contains s.rule.lhs || s.rule.lhs == .NumericLiteral) = true) :
    rhsAvoidsAnc s.alt.rhs = true := by
  rw [← glData_eq] at hs
  obtain ⟨hpinCert, hblkCert⟩ := Bool.and_eq_true_iff.mp lexRulesAvoidCert_true
  have hmemZip1 : ∀ {α : Type} {x : α} {i : Nat} {xs : List α} {k : Nat},
      (x, i) ∈ xs.zipIdx k → x ∈ xs := by
    intro α x i xs
    induction xs with
    | nil => intro _ h; cases h
    | cons y tl ih =>
      intro k h
      rcases List.mem_cons.mp h with heq | htl
      · exact (Prod.mk.inj heq).1 ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih htl)
  have hfromRule : ∀ (g0 : GrammarId) (r : Rule),
      (if !numLitAncNTs.contains r.lhs || r.lhs == .NumericLiteral then
        (writtenAlts r).all fun a => rhsAvoidsAnc a.rhs else true) = true →
      ∀ x ∈ srcsOf g0 r,
        (!numLitAncNTs.contains x.rule.lhs || x.rule.lhs == .NumericLiteral) = true →
        rhsAvoidsAnc x.alt.rhs = true := by
    intro g0 r hrCert x hx hxLhs
    simp only [srcsOf, List.mem_map] at hx
    obtain ⟨⟨alt0, idx0⟩, hmemZip, rfl⟩ := hx
    dsimp only at hxLhs ⊢
    simp only [hxLhs, ↓reduceIte] at hrCert
    exact List.all_eq_true.mp hrCert alt0 (hmemZip1 hmemZip)
  have hpin : ∀ x ∈ glData.pinned .lexical n,
      (!numLitAncNTs.contains x.rule.lhs || x.rule.lhs == .NumericLiteral) = true →
      rhsAvoidsAnc x.alt.rhs = true := by
    intro x hx hxLhs
    unfold GL.pinned at hx
    cases hf : (glData.rulesOf .lexical).find? (·.lhs == n) with
    | none => simp [hf, baseGrammar] at hx
    | some r =>
      rw [hf] at hx
      exact hfromRule .lexical r (List.all_eq_true.mp hpinCert r (List.mem_of_find?_eq_some hf)) x hx hxLhs
  have hov : ∀ (bs : List (Block × OverlayMode)) (acc : List Src),
      (∀ pm ∈ bs, pm.1 ∈ glData.blocks ∧ ∃ sec md cd, pm.1.kind = .overlay sec md cd ∧ overlayGrammar sec == .lexical) →
      (∀ x ∈ acc, (!numLitAncNTs.contains x.rule.lhs || x.rule.lhs == .NumericLiteral) = true → rhsAvoidsAnc x.alt.rhs = true) →
      ∀ x ∈ bs.foldl (fun a (b, m) =>
        match b.rules.find? (·.lhs == n), m with
        | none, _ => a
        | some r, .extend => a ++ (srcsOf .annexB r).filter fun s' => !a.any (·.alt == s'.alt)
        | some r, .replace => srcsOf .annexB r) acc,
      (!numLitAncNTs.contains x.rule.lhs || x.rule.lhs == .NumericLiteral) = true →
      rhsAvoidsAnc x.alt.rhs = true := by
    intro bs
    induction bs with
    | nil => intro acc _ hacc x hx; exact hacc x hx
    | cons hd tl ih =>
      rcases hd with ⟨b, m⟩
      intro acc hbs hacc x hx
      obtain ⟨hbMem, sec, md, cd, hbk, hog⟩ := hbs (b, m) (List.mem_cons_self ..)
      have hbs' := fun pm hpm => hbs pm (List.mem_cons_of_mem _ hpm)
      have hbOk := List.all_eq_true.mp hblkCert b hbMem
      rw [hbk] at hbOk; simp only [hog, Bool.not_true, Bool.false_or] at hbOk
      simp only [List.foldl_cons] at hx
      cases hfr : b.rules.find? (·.lhs == n) with
      | none => rw [hfr] at hx; exact ih acc hbs' hacc x hx
      | some r =>
        rw [hfr] at hx
        have hrOk := hfromRule .annexB r (List.all_eq_true.mp hbOk r (List.mem_of_find?_eq_some hfr))
        cases m with
        | extend =>
          apply ih _ hbs' _ x hx
          intro y hy
          rcases List.mem_append.mp hy with h1 | h2
          · exact hacc y h1
          · exact hrOk y (List.mem_filter.mp h2).1
        | replace => exact ih _ hbs' hrOk x hx
  have hbsMem : ∀ pm ∈ glData.overlays cx .lexical,
      pm.1 ∈ glData.blocks ∧ ∃ sec md cd, pm.1.kind = .overlay sec md cd ∧ overlayGrammar sec == .lexical := by
    intro pm hpm
    unfold GL.overlays at hpm
    by_cases hany : (!cx.annexB.any) = true
    · simp [hany] at hpm
    · simp only [hany, Bool.false_eq_true, ↓reduceIte, List.mem_filterMap] at hpm
      obtain ⟨b, hbMem, hfb⟩ := hpm
      cases hbk : b.kind with
      | main | supplemental _ => rw [hbk] at hfb; cases hfb
      | overlay sec md cd =>
        rw [hbk] at hfb; dsimp only at hfb
        by_cases hif : (overlayGrammar sec == .lexical && cx.annexB.has sec && condHolds cx cd) = true
        · simp only [hif, ↓reduceIte, Option.some.injEq] at hfb
          subst hfb
          simp only [Bool.and_eq_true] at hif
          exact ⟨hbMem, sec, md, cd, hbk, hif.1.1⟩
        · simp [hif] at hfb
  exact hov (glData.overlays cx .lexical) (glData.pinned .lexical n) hbsMem hpin s hs hn

private theorem plain_has_numLit_false (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (a b : Nat) :
    ∀ (sz : Nat) {n : NT} {ps : List Param} {x y : Nat} {dt : DTree},
      sizeOf dt ≤ sz →
      numLitAncNTs.contains n = false →
      (lexSpec cs cx).PlainDerives n ps x y dt →
      dt.toTree.has .NumericLiteral a b = false := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    intro n ps x y dt hsz hnNot hd
    cases hd with
    | node s hs _ _ _ hsw =>
      have hsSpec := lex_mem_alts hok hs
      have hlhs := (alt_lhs_and_opts hok hsSpec).1
      have hcert := lex_alt_rhsAvoidsAnc hsSpec (by rw [hlhs, hnNot]; rfl)
      have hnNe : (n == .NumericLiteral) = false := by
        cases h : n == .NumericLiteral with
        | false => rfl
        | true => rw [beq_iff_eq.mp h] at hnNot; cases hnNot
      rw [DTree.toTree, tree_has_node]
      simp only [hnNe, Bool.false_and, Bool.false_or]
      have hswKids : ∀ (is0 : List Item) {k0 : Nat} {p0 q0 : Nat} {m0 : List Bool} {ks0 : List DTree},
          rhsAvoidsAnc is0 = true →
          sizeOf ks0 < sz →
          (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) s ps k0 is0 p0 q0 m0 ks0 →
          (ks0.map DTree.toTree).any (Tree.has .NumericLiteral a b) = false := by
        intro is0
        induction is0 with
        | nil =>
          intro _ _ _ _ _ _ _ hsw0
          cases hsw0; rfl
        | cons it1 rest ihs =>
          intro k0 p0 q0 m0 ks0 hav hksz hsw0
          cases hsw0 with
          | absent hr =>
            cases ‹Sym› with
            | t _ => exact ihs hav hksz hr
            | nt _ _ => exact ihs (Bool.and_eq_true_iff.mp hav).2 hksz hr
          | term _ hr =>
            simp only [List.map_cons, DTree.toTree, List.any_cons, Tree.has, Bool.false_or]
            exact ihs hav (by simp +arith only [List.cons.sizeOf_spec] at hksz; omega) hr
          | nt _ hdSub _ _ hr =>
            dsimp only [rhsAvoidsAnc] at hav
            obtain ⟨hmNot, havR⟩ := Bool.and_eq_true_iff.mp hav
            rw [Bool.not_eq_true'] at hmNot
            have hsubF := ih (sz - 1) (by omega) (by simp +arith only [List.cons.sizeOf_spec] at hksz; omega) hmNot hdSub
            have hrestF := ihs havR (by simp +arith only [List.cons.sizeOf_spec] at hksz; omega) hr
            simp only [List.map_cons, List.any_cons, hsubF, Bool.false_or]
            exact hrestF
          | leaf _ hl _ _ _ => exact nomatch hl
          | butNotT _ _ hr =>
            simp only [List.map_cons, DTree.toTree, List.any_cons, Tree.has, Bool.false_or]
            exact ihs hav (by simp +arith only [List.cons.sizeOf_spec] at hksz; omega) hr
          | butNotN _ hdSub _ _ hr =>
            dsimp only [rhsAvoidsAnc] at hav
            obtain ⟨hmNot, havR⟩ := Bool.and_eq_true_iff.mp hav
            rw [Bool.not_eq_true'] at hmNot
            have hsubF := ih (sz - 1) (by omega) (by simp +arith only [List.cons.sizeOf_spec] at hksz; omega) hmNot hdSub
            have hrestF := ihs havR (by simp +arith only [List.cons.sizeOf_spec] at hksz; omega) hr
            simp only [List.map_cons, List.any_cons, hsubF, Bool.false_or]
            exact hrestF
          | butNotLeaf _ hl _ _ _ => exact nomatch hl
          | phrase _ hr =>
            simp only [List.map_cons, DTree.toTree, List.any_cons, Tree.has, Bool.false_or]
            exact ihs hav (by simp +arith only [List.cons.sizeOf_spec] at hksz; omega) hr
          | look _ hr | noLT _ hr | empty hr | onlyIf hr => exact ihs hav hksz hr
      exact hswKids s.alt.rhs hcert (by simp +arith only [DTree.node.sizeOf_spec] at hsz; omega) hsw

private theorem plain_numericLiteral_has_true {cx : Ctx} {cs : Array Nat} {a b : Nat} {dt : DTree}
    (hd : (lexSpec cs cx).PlainDerives .NumericLiteral [] a b dt) :
    dt.toTree.has .NumericLiteral a b = true := by
  cases hd with
  | node _ _ _ _ _ _ =>
    rw [DTree.toTree, tree_has_node]
    simp

private theorem tokClass_has_numLit (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {cls : NT} (hcls : cls ∈ allTokClasses) {a b : Nat} {dt : DTree}
    (hd : (lexSpec cs cx).PlainDerives cls [] a b dt) :
    dt.toTree.has .NumericLiteral a b = (cls == .NumericLiteral) := by
  by_cases hnum : cls = .NumericLiteral
  · subst hnum; simp [plain_numericLiteral_has_true hd]
  · have hne : (cls == .NumericLiteral) = false := Bool.eq_false_iff.mpr (fun h => hnum (beq_iff_eq.mp h))
    rw [hne]
    have hnotAnc : numLitAncNTs.contains cls = false := by
      simp only [allTokClasses, List.mem_cons, List.not_mem_nil, or_false] at hcls
      rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact absurd rfl hnum | rfl
    exact plain_has_numLit_false hok a b (sizeOf dt) (Nat.le_refl _) hnotAnc hd

/-! ### `InputElement*` packing and unpacking -/

private theorem kind_of_plain_wrap {cx : Ctx} {cs : Array Nat} {g sub : NT} {idG : Nat} {sG : Src}
    {a b : Nat} {dtSub : DTree} (hdSub : (lexSpec cs cx).PlainDerives sub [] a b dtSub) :
    Element.kind ⟨a, b, g, (DTree.node g idG sG [] a b [] [dtSub]).toTree⟩ = some sub := by
  cases hdSub with
  | node _ _ _ _ _ _ => simp [Element.kind, DTree.toTree, Tree.nt?]

private theorem isToken_false_of_nonToken {a b : Nat} {g sub : NT} {tree : Tree}
    (hk : Element.kind ⟨a, b, g, tree⟩ = some sub)
    (hsub : sub = .WhiteSpace ∨ sub = .LineTerminator ∨ sub = .Comment ∨ sub = .HashbangComment ∨ sub = .HTMLCloseComment) :
    Element.isToken ⟨a, b, g, tree⟩ = false := by
  unfold Element.isToken
  rw [hk]
  rcases hsub with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem isToken_true_of_tokKind {a b : Nat} {g sub : NT} {tree : Tree}
    (hk : Element.kind ⟨a, b, g, tree⟩ = some sub)
    (hsub : sub = .CommonToken ∨ sub = .DivPunctuator ∨ sub = .RightBracePunctuator ∨
            sub = .RegularExpressionLiteral ∨ sub = .TemplateSubstitutionTail) :
    Element.isToken ⟨a, b, g, tree⟩ = true := by
  unfold Element.isToken
  rw [hk]
  rcases hsub with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem wrap_has_numLit {g : NT} (hg : g ≠ .NumericLiteral) {idG : Nat} {sG : Src}
    {a b : Nat} {dtSub : DTree} :
    (DTree.node g idG sG [] a b [] [dtSub]).toTree.has .NumericLiteral a b =
      dtSub.toTree.has .NumericLiteral a b := by
  have hne : (g == .NumericLiteral) = false := Bool.eq_false_iff.mpr (fun h => hg (beq_iff_eq.mp h))
  rw [DTree.toTree, List.map_cons, List.map_nil, tree_has_node]
  simp [hne]

private theorem seqWith_single_nt {cx : Ctx} {cs : Array Nat} {s : Src} {ps : List Param}
    {sub : NT} {a b : Nat} {m : List Bool} {kids : List DTree}
    (h : (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) s ps 0 [.sym (.nt sub []) false] a b m kids) :
    ∃ dtSub, m = [] ∧ kids = [dtSub] ∧ (lexSpec cs cx).PlainDerives sub [] a b dtSub := by
  cases h with
  | leaf _ hl _ _ _ => exact nomatch hl
  | nt _ hd _ _ hnil => cases hnil; exact ⟨_, rfl, rfl, hd⟩

theorem packNonToken (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {g sub : NT} (hg : isLexGoal g = true) {a b : Nat} (ha : a ≤ cs.size) {dtSub : DTree}
    (hsub : sub = .WhiteSpace ∨ sub = .LineTerminator ∨ sub = .Comment ∨
            (g = .InputElementHashbangOrRegExp ∧ sub = .HashbangComment) ∨
            (g = .InputElementHashbangOrRegExp ∧ Lex.html cx = true ∧ sub = .HTMLCloseComment))
    (hdSub : (lexSpec cs cx).PlainDerives sub [] a b dtSub) :
    ∃ tree,
      LexDerives cx cs g [] a b tree ∧
      Element.kind ⟨a, b, g, tree⟩ = some sub ∧
      Element.isToken ⟨a, b, g, tree⟩ = false ∧
      tree.has .NumericLiteral a b = false := by
  have hgNeNum : g ≠ .NumericLiteral := by
    unfold isLexGoal at hg
    simp only [Bool.or_eq_true, beq_iff_eq] at hg
    rcases hg with (((rfl | rfl) | rfl) | rfl) | rfl <;> decide
  have hsubNotAnc : numLitAncNTs.contains sub = false := by
    rcases hsub with rfl | rfl | rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
  have hsubHasF : dtSub.toTree.has .NumericLiteral a b = false :=
    plain_has_numLit_false hok a b (sizeOf dtSub) (Nat.le_refl _) hsubNotAnc hdSub
  have hexAlt : ∃ sG ∈ Ecma.Spec.gl.alts cx .lexical g, sG.alt = ⟨[], [.sym (.nt sub []) false], none⟩ := by
    unfold isLexGoal at hg
    simp only [Bool.or_eq_true, beq_iff_eq] at hg
    rcases hsub with rfl | rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, hhtml, rfl⟩
    · rcases hg with (((rfl | rfl) | rfl) | rfl) | rfl
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.1 alts_cert_core.2.1) 0 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.1 alts_cert_core.2.2.2.1) 0 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.1 alts_cert_core.2.2.2.2.2.1) 0 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.2.2.1 alts_cert_core.2.2.2.2.2.2.2.1) 0 rfl, rfl⟩
      · cases h : Lex.html cx with
        | false => exact ⟨_, mem_alts_of_get? (alts_html_false_eq h alts_cert_core.2.2.2.2.2.2.2.2.1) 0 rfl, rfl⟩
        | true => exact ⟨_, mem_alts_of_get? (alts_html_true_eq h alts_cert_core.2.2.2.2.2.2.2.2.2) 0 rfl, rfl⟩
    · rcases hg with (((rfl | rfl) | rfl) | rfl) | rfl
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.1 alts_cert_core.2.1) 1 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.1 alts_cert_core.2.2.2.1) 1 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.1 alts_cert_core.2.2.2.2.2.1) 1 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.2.2.1 alts_cert_core.2.2.2.2.2.2.2.1) 1 rfl, rfl⟩
      · cases h : Lex.html cx with
        | false => exact ⟨_, mem_alts_of_get? (alts_html_false_eq h alts_cert_core.2.2.2.2.2.2.2.2.1) 1 rfl, rfl⟩
        | true => exact ⟨_, mem_alts_of_get? (alts_html_true_eq h alts_cert_core.2.2.2.2.2.2.2.2.2) 1 rfl, rfl⟩
    · rcases hg with (((rfl | rfl) | rfl) | rfl) | rfl
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.1 alts_cert_core.2.1) 2 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.1 alts_cert_core.2.2.2.1) 2 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.1 alts_cert_core.2.2.2.2.2.1) 2 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.2.2.1 alts_cert_core.2.2.2.2.2.2.2.1) 2 rfl, rfl⟩
      · cases h : Lex.html cx with
        | false => exact ⟨_, mem_alts_of_get? (alts_html_false_eq h alts_cert_core.2.2.2.2.2.2.2.2.1) 2 rfl, rfl⟩
        | true => exact ⟨_, mem_alts_of_get? (alts_html_true_eq h alts_cert_core.2.2.2.2.2.2.2.2.2) 2 rfl, rfl⟩
    · cases h : Lex.html cx with
      | false => exact ⟨_, mem_alts_of_get? (alts_html_false_eq h alts_cert_core.2.2.2.2.2.2.2.2.1) 4 rfl, rfl⟩
      | true => exact ⟨_, mem_alts_of_get? (alts_html_true_eq h alts_cert_core.2.2.2.2.2.2.2.2.2) 4 rfl, rfl⟩
    · exact ⟨_, mem_alts_of_get? (alts_html_true_eq hhtml alts_cert_core.2.2.2.2.2.2.2.2.2) 6 rfl, rfl⟩
  obtain ⟨sG, hsG, haltG⟩ := hexAlt
  have hneSub : (altsOf cx .lexical sub).isEmpty = false := by
    cases hdSub with | node s0 hs0 _ _ _ _ => exact altsOf_nonempty_of_mem hok (lex_mem_alts hok hs0)
  have hswG : (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sG [] 0 sG.alt.rhs a b [] [dtSub] := by
    rw [haltG]; exact .nt hneSub hdSub rfl trivial .nil
  obtain ⟨idG, hdG⟩ := mkLexPlainSimple hok hsG (by rw [haltG]; rfl) hswG
  have ⟨_, _, hderG⟩ := lexPlain_to_derives hok ha hdG
  have hkind : Element.kind ⟨a, b, g, (DTree.node g idG sG [] a b [] [dtSub]).toTree⟩ = some sub :=
    kind_of_plain_wrap hdSub
  have hisTokF : Element.isToken ⟨a, b, g, (DTree.node g idG sG [] a b [] [dtSub]).toTree⟩ = false := by
    apply isToken_false_of_nonToken hkind
    rcases hsub with rfl | rfl | rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨_, hderG, hkind, hisTokF, ?_⟩
  rw [wrap_has_numLit hgNeNum, hsubHasF]

theorem packToken (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {g cls : NT} (hg : isLexGoal g = true) (hcls : cls ∈ Lex.classes g)
    {a b : Nat} (ha : a ≤ cs.size) {dtCls : DTree}
    (hdCls : (lexSpec cs cx).PlainDerives cls [] a b dtCls) :
    ∃ tree,
      LexDerives cx cs g [] a b tree ∧
      Element.isToken ⟨a, b, g, tree⟩ = true ∧
      tree.has .NumericLiteral a b = (cls == .NumericLiteral) := by
  have hgNeNum : g ≠ .NumericLiteral := by
    unfold isLexGoal at hg
    simp only [Bool.or_eq_true, beq_iff_eq] at hg
    rcases hg with (((rfl | rfl) | rfl) | rfl) | rfl <;> decide
  have hclsAll := classes_sub_allTokClasses g cls hcls
  have hhasCls := tokClass_has_numLit hok hclsAll hdCls
  have hneCls : (altsOf cx .lexical cls).isEmpty = false := by
    cases hdCls with | node s0 hs0 _ _ _ _ => exact altsOf_nonempty_of_mem hok (lex_mem_alts hok hs0)
  have haltsCT := alts_fixed_eq (cx := cx) alts_cert_tokens.1 alts_cert_tokens.2.1
  have haltsTmpl := alts_fixed_eq (cx := cx) alts_cert_tokens.2.2.1 alts_cert_tokens.2.2.2.1
  have haltsTail := alts_fixed_eq (cx := cx) alts_cert_tokens.2.2.2.2.1 alts_cert_tokens.2.2.2.2.2.1
  -- Build intermediate child `sub` of `g`:
  have hmid : ∃ sub dtMid,
      (sub = .CommonToken ∨ sub = .DivPunctuator ∨ sub = .RightBracePunctuator ∨
       sub = .RegularExpressionLiteral ∨ sub = .TemplateSubstitutionTail) ∧
      (∃ sG ∈ Ecma.Spec.gl.alts cx .lexical g, sG.alt = ⟨[], [.sym (.nt sub []) false], none⟩) ∧
      (lexSpec cs cx).PlainDerives sub [] a b dtMid ∧
      dtMid.toTree.has .NumericLiteral a b = (cls == .NumericLiteral) := by
    have hctGoal : ∃ sG ∈ Ecma.Spec.gl.alts cx .lexical g, sG.alt = ⟨[], [.sym (.nt .CommonToken []) false], none⟩ := by
      unfold isLexGoal at hg; simp only [Bool.or_eq_true, beq_iff_eq] at hg
      rcases hg with (((rfl | rfl) | rfl) | rfl) | rfl
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.1 alts_cert_core.2.1) 3 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.1 alts_cert_core.2.2.2.1) 3 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.1 alts_cert_core.2.2.2.2.2.1) 3 rfl, rfl⟩
      · exact ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.2.2.1 alts_cert_core.2.2.2.2.2.2.2.1) 3 rfl, rfl⟩
      · cases h : Lex.html cx with
        | false => exact ⟨_, mem_alts_of_get? (alts_html_false_eq h alts_cert_core.2.2.2.2.2.2.2.2.1) 3 rfl, rfl⟩
        | true => exact ⟨_, mem_alts_of_get? (alts_html_true_eq h alts_cert_core.2.2.2.2.2.2.2.2.2) 3 rfl, rfl⟩
    unfold Lex.classes at hcls
    rw [List.mem_append] at hcls
    rcases hcls with hcom | hgoalRest
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcom
      rcases hcom with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · let sCT : Src := ⟨.lexical, Gen.Lexical.CommonToken, 0, ⟨[], [.sym (.nt .IdentifierName []) false], none⟩⟩
        have hsCT := mem_alts_of_get? haltsCT (x := sCT) 0 rfl
        obtain ⟨idCT, hdCT⟩ := mkLexPlainSimple hok hsCT rfl (.nt hneCls hdCls rfl trivial .nil)
        exact ⟨.CommonToken, _, Or.inl rfl, hctGoal, hdCT, (wrap_has_numLit (by decide)).trans hhasCls⟩
      · let sCT : Src := ⟨.lexical, Gen.Lexical.CommonToken, 1, ⟨[], [.sym (.nt .PrivateIdentifier []) false], none⟩⟩
        have hsCT := mem_alts_of_get? haltsCT (x := sCT) 1 rfl
        obtain ⟨idCT, hdCT⟩ := mkLexPlainSimple hok hsCT rfl (.nt hneCls hdCls rfl trivial .nil)
        exact ⟨.CommonToken, _, Or.inl rfl, hctGoal, hdCT, (wrap_has_numLit (by decide)).trans hhasCls⟩
      · let sCT : Src := ⟨.lexical, Gen.Lexical.CommonToken, 2, ⟨[], [.sym (.nt .Punctuator []) false], none⟩⟩
        have hsCT := mem_alts_of_get? haltsCT (x := sCT) 2 rfl
        obtain ⟨idCT, hdCT⟩ := mkLexPlainSimple hok hsCT rfl (.nt hneCls hdCls rfl trivial .nil)
        exact ⟨.CommonToken, _, Or.inl rfl, hctGoal, hdCT, (wrap_has_numLit (by decide)).trans hhasCls⟩
      · let sCT : Src := ⟨.lexical, Gen.Lexical.CommonToken, 3, ⟨[], [.sym (.nt .NumericLiteral []) false], none⟩⟩
        have hsCT := mem_alts_of_get? haltsCT (x := sCT) 3 rfl
        obtain ⟨idCT, hdCT⟩ := mkLexPlainSimple hok hsCT rfl (.nt hneCls hdCls rfl trivial .nil)
        exact ⟨.CommonToken, _, Or.inl rfl, hctGoal, hdCT, (wrap_has_numLit (by decide)).trans hhasCls⟩
      · let sCT : Src := ⟨.lexical, Gen.Lexical.CommonToken, 4, ⟨[], [.sym (.nt .StringLiteral []) false], none⟩⟩
        have hsCT := mem_alts_of_get? haltsCT (x := sCT) 4 rfl
        obtain ⟨idCT, hdCT⟩ := mkLexPlainSimple hok hsCT rfl (.nt hneCls hdCls rfl trivial .nil)
        exact ⟨.CommonToken, _, Or.inl rfl, hctGoal, hdCT, (wrap_has_numLit (by decide)).trans hhasCls⟩
      · let sT : Src := ⟨.lexical, Gen.Lexical.Template, 0, ⟨[], [.sym (.nt .NoSubstitutionTemplate []) false], none⟩⟩
        let sCT : Src := ⟨.lexical, Gen.Lexical.CommonToken, 5, ⟨[], [.sym (.nt .Template []) false], none⟩⟩
        have hsT := mem_alts_of_get? haltsTmpl (x := sT) 0 rfl
        have hsCT := mem_alts_of_get? haltsCT (x := sCT) 5 rfl
        obtain ⟨_, hdT⟩ := mkLexPlainSimple hok hsT rfl (.nt hneCls hdCls rfl trivial .nil)
        obtain ⟨_, hdCT⟩ := mkLexPlainSimple hok hsCT rfl (.nt (altsOf_nonempty_of_mem hok hsT) hdT rfl trivial .nil)
        exact ⟨.CommonToken, _, Or.inl rfl, hctGoal, hdCT,
          (wrap_has_numLit (by decide)).trans ((wrap_has_numLit (by decide)).trans hhasCls)⟩
      · let sT : Src := ⟨.lexical, Gen.Lexical.Template, 1, ⟨[], [.sym (.nt .TemplateHead []) false], none⟩⟩
        let sCT : Src := ⟨.lexical, Gen.Lexical.CommonToken, 5, ⟨[], [.sym (.nt .Template []) false], none⟩⟩
        have hsT := mem_alts_of_get? haltsTmpl (x := sT) 1 rfl
        have hsCT := mem_alts_of_get? haltsCT (x := sCT) 5 rfl
        obtain ⟨_, hdT⟩ := mkLexPlainSimple hok hsT rfl (.nt hneCls hdCls rfl trivial .nil)
        obtain ⟨_, hdCT⟩ := mkLexPlainSimple hok hsCT rfl (.nt (altsOf_nonempty_of_mem hok hsT) hdT rfl trivial .nil)
        exact ⟨.CommonToken, _, Or.inl rfl, hctGoal, hdCT,
          (wrap_has_numLit (by decide)).trans ((wrap_has_numLit (by decide)).trans hhasCls)⟩
    · unfold isLexGoal at hg; simp only [Bool.or_eq_true, beq_iff_eq] at hg
      rcases hg with (((rfl | rfl) | rfl) | rfl) | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hgoalRest
        rcases hgoalRest with rfl | rfl
        · exact ⟨.DivPunctuator, dtCls, Or.inr (Or.inl rfl),
            ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.1 alts_cert_core.2.1) 4 rfl, rfl⟩, hdCls, hhasCls⟩
        · exact ⟨.RightBracePunctuator, dtCls, Or.inr (Or.inr (Or.inl rfl)),
            ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.1 alts_cert_core.2.1) 5 rfl, rfl⟩, hdCls, hhasCls⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hgoalRest
        rcases hgoalRest with rfl | rfl
        · exact ⟨.RightBracePunctuator, dtCls, Or.inr (Or.inr (Or.inl rfl)),
            ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.1 alts_cert_core.2.2.2.1) 4 rfl, rfl⟩, hdCls, hhasCls⟩
        · exact ⟨.RegularExpressionLiteral, dtCls, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
            ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.1 alts_cert_core.2.2.2.1) 5 rfl, rfl⟩, hdCls, hhasCls⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hgoalRest
        rcases hgoalRest with rfl | rfl | rfl
        · exact ⟨.RegularExpressionLiteral, dtCls, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
            ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.1 alts_cert_core.2.2.2.2.2.1) 4 rfl, rfl⟩, hdCls, hhasCls⟩
        · let sTl : Src := ⟨.lexical, Gen.Lexical.TemplateSubstitutionTail, 0, ⟨[], [.sym (.nt .TemplateMiddle []) false], none⟩⟩
          have hsTl := mem_alts_of_get? haltsTail (x := sTl) 0 rfl
          obtain ⟨_, hdTl⟩ := mkLexPlainSimple hok hsTl rfl (.nt hneCls hdCls rfl trivial .nil)
          exact ⟨.TemplateSubstitutionTail, _, Or.inr (Or.inr (Or.inr (Or.inr rfl))),
            ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.1 alts_cert_core.2.2.2.2.2.1) 5 rfl, rfl⟩,
            hdTl, (wrap_has_numLit (by decide)).trans hhasCls⟩
        · let sTl : Src := ⟨.lexical, Gen.Lexical.TemplateSubstitutionTail, 1, ⟨[], [.sym (.nt .TemplateTail []) false], none⟩⟩
          have hsTl := mem_alts_of_get? haltsTail (x := sTl) 1 rfl
          obtain ⟨_, hdTl⟩ := mkLexPlainSimple hok hsTl rfl (.nt hneCls hdCls rfl trivial .nil)
          exact ⟨.TemplateSubstitutionTail, _, Or.inr (Or.inr (Or.inr (Or.inr rfl))),
            ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.1 alts_cert_core.2.2.2.2.2.1) 5 rfl, rfl⟩,
            hdTl, (wrap_has_numLit (by decide)).trans hhasCls⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hgoalRest
        rcases hgoalRest with rfl | rfl | rfl
        · exact ⟨.DivPunctuator, dtCls, Or.inr (Or.inl rfl),
            ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.2.2.1 alts_cert_core.2.2.2.2.2.2.2.1) 4 rfl, rfl⟩, hdCls, hhasCls⟩
        · let sTl : Src := ⟨.lexical, Gen.Lexical.TemplateSubstitutionTail, 0, ⟨[], [.sym (.nt .TemplateMiddle []) false], none⟩⟩
          have hsTl := mem_alts_of_get? haltsTail (x := sTl) 0 rfl
          obtain ⟨_, hdTl⟩ := mkLexPlainSimple hok hsTl rfl (.nt hneCls hdCls rfl trivial .nil)
          exact ⟨.TemplateSubstitutionTail, _, Or.inr (Or.inr (Or.inr (Or.inr rfl))),
            ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.2.2.1 alts_cert_core.2.2.2.2.2.2.2.1) 5 rfl, rfl⟩,
            hdTl, (wrap_has_numLit (by decide)).trans hhasCls⟩
        · let sTl : Src := ⟨.lexical, Gen.Lexical.TemplateSubstitutionTail, 1, ⟨[], [.sym (.nt .TemplateTail []) false], none⟩⟩
          have hsTl := mem_alts_of_get? haltsTail (x := sTl) 1 rfl
          obtain ⟨_, hdTl⟩ := mkLexPlainSimple hok hsTl rfl (.nt hneCls hdCls rfl trivial .nil)
          exact ⟨.TemplateSubstitutionTail, _, Or.inr (Or.inr (Or.inr (Or.inr rfl))),
            ⟨_, mem_alts_of_get? (alts_fixed_eq alts_cert_core.2.2.2.2.2.2.1 alts_cert_core.2.2.2.2.2.2.2.1) 5 rfl, rfl⟩,
            hdTl, (wrap_has_numLit (by decide)).trans hhasCls⟩
      · simp only [List.mem_singleton] at hgoalRest
        subst hgoalRest
        have hsGRE : ∃ sG ∈ Ecma.Spec.gl.alts cx .lexical .InputElementHashbangOrRegExp,
            sG.alt = ⟨[], [.sym (.nt .RegularExpressionLiteral []) false], none⟩ := by
          cases h : Lex.html cx with
          | false => exact ⟨_, mem_alts_of_get? (alts_html_false_eq h alts_cert_core.2.2.2.2.2.2.2.2.1) 5 rfl, rfl⟩
          | true => exact ⟨_, mem_alts_of_get? (alts_html_true_eq h alts_cert_core.2.2.2.2.2.2.2.2.2) 5 rfl, rfl⟩
        exact ⟨.RegularExpressionLiteral, dtCls, Or.inr (Or.inr (Or.inr (Or.inl rfl))), hsGRE, hdCls, hhasCls⟩
  obtain ⟨sub, dtMid, hsubTok, ⟨sG, hsG, haltG⟩, hdMid, hhasMid⟩ := hmid
  have hneMid : (altsOf cx .lexical sub).isEmpty = false := by
    cases hdMid with | node s0 hs0 _ _ _ _ => exact altsOf_nonempty_of_mem hok (lex_mem_alts hok hs0)
  have hswG : (lexSpec cs cx).SeqWith (fun _ _ _ _ => True) sG [] 0 sG.alt.rhs a b [] [dtMid] := by
    rw [haltG]; exact .nt hneMid hdMid rfl trivial .nil
  obtain ⟨idG, hdG⟩ := mkLexPlainSimple hok hsG (by rw [haltG]; rfl) hswG
  have ⟨_, _, hderG⟩ := lexPlain_to_derives hok ha hdG
  have hkind : Element.kind ⟨a, b, g, (DTree.node g idG sG [] a b [] [dtMid]).toTree⟩ = some sub :=
    kind_of_plain_wrap hdMid
  refine ⟨_, hderG, isToken_true_of_tokKind hkind hsubTok, ?_⟩
  rw [wrap_has_numLit hgNeNum, hhasMid]

theorem unpackInputElement (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {g : NT} (hg : isLexGoal g = true) {a b : Nat} (hb : b ≤ cs.size) {tree : Tree}
    (hd : LexDerives cx cs g [] a b tree) :
    (Element.isToken ⟨a, b, g, tree⟩ = false ∧ tree.has .NumericLiteral a b = false ∧
      ((Element.kind ⟨a, b, g, tree⟩ = some .WhiteSpace ∧ ∃ dt, (lexSpec cs cx).PlainDerives .WhiteSpace [] a b dt) ∨
       (Element.kind ⟨a, b, g, tree⟩ = some .LineTerminator ∧ ∃ dt, (lexSpec cs cx).PlainDerives .LineTerminator [] a b dt) ∨
       (Element.kind ⟨a, b, g, tree⟩ = some .Comment ∧ ∃ dt, (lexSpec cs cx).PlainDerives .Comment [] a b dt) ∨
       (g = .InputElementHashbangOrRegExp ∧ Element.kind ⟨a, b, g, tree⟩ = some .HashbangComment ∧ ∃ dt, (lexSpec cs cx).PlainDerives .HashbangComment [] a b dt) ∨
       (g = .InputElementHashbangOrRegExp ∧ Lex.html cx = true ∧ Element.kind ⟨a, b, g, tree⟩ = some .HTMLCloseComment ∧ ∃ dt, (lexSpec cs cx).PlainDerives .HTMLCloseComment [] a b dt))) ∨
    (Element.isToken ⟨a, b, g, tree⟩ = true ∧
      ∃ cls ∈ Lex.classes g, ∃ dt, (lexSpec cs cx).PlainDerives cls [] a b dt ∧
        tree.has .NumericLiteral a b = (cls == .NumericLiteral)) := by
  obtain ⟨dtG, rfl, hplG⟩ := lexDerives_to_plain hok hb hd
  have hgNeNum : g ≠ .NumericLiteral := by
    unfold isLexGoal at hg; simp only [Bool.or_eq_true, beq_iff_eq] at hg
    rcases hg with (((rfl | rfl) | rfl) | rfl) | rfl <;> decide
  have haltsCT := alts_fixed_eq (cx := cx) alts_cert_tokens.1 alts_cert_tokens.2.1
  have haltsTmpl := alts_fixed_eq (cx := cx) alts_cert_tokens.2.2.1 alts_cert_tokens.2.2.2.1
  have haltsTail := alts_fixed_eq (cx := cx) alts_cert_tokens.2.2.2.2.1 alts_cert_tokens.2.2.2.2.2.1
  -- Classify the single child `sub` of `dtG`:
  have hchild : ∃ idG sG sub dtSub,
      dtG = .node g idG sG [] a b [] [dtSub] ∧
      (lexSpec cs cx).PlainDerives sub [] a b dtSub ∧
      ((sub = .WhiteSpace ∨ sub = .LineTerminator ∨ sub = .Comment ∨
        (g = .InputElementHashbangOrRegExp ∧ sub = .HashbangComment) ∨
        (g = .InputElementHashbangOrRegExp ∧ Lex.html cx = true ∧ sub = .HTMLCloseComment)) ∨
       (sub = .CommonToken ∨
        (sub ∈ Lex.classes g ∧ (sub = .DivPunctuator ∨ sub = .RightBracePunctuator ∨ sub = .RegularExpressionLiteral)) ∨
        (sub = .TemplateSubstitutionTail ∧ (g = .InputElementRegExpOrTemplateTail ∨ g = .InputElementTemplateTail)))) := by
    cases hplG with
    | node sG hsG _ _ _ hswG =>
      have hsG := lex_mem_alts hok hsG
      unfold isLexGoal at hg; simp only [Bool.or_eq_true, beq_iff_eq] at hg
      rcases hg with (((rfl | rfl) | rfl) | rfl) | rfl
      · rw [alts_fixed_eq alts_cert_core.1 alts_cert_core.2.1] at hsG
        simp only [srcsOf, writtenAlts, Gen.Lexical.InputElementDiv, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsG
        rcases hsG with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .WhiteSpace, _, rfl, hdS, Or.inl (Or.inl rfl)⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .LineTerminator, _, rfl, hdS, Or.inl (Or.inr (Or.inl rfl))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .Comment, _, rfl, hdS, Or.inl (Or.inr (Or.inr (Or.inl rfl)))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .CommonToken, _, rfl, hdS, Or.inr (Or.inl rfl)⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .DivPunctuator, _, rfl, hdS, Or.inr (Or.inr (Or.inl ⟨by decide, Or.inl rfl⟩))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .RightBracePunctuator, _, rfl, hdS, Or.inr (Or.inr (Or.inl ⟨by decide, Or.inr (Or.inl rfl)⟩))⟩
      · rw [alts_fixed_eq alts_cert_core.2.2.1 alts_cert_core.2.2.2.1] at hsG
        simp only [srcsOf, writtenAlts, Gen.Lexical.InputElementRegExp, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsG
        rcases hsG with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .WhiteSpace, _, rfl, hdS, Or.inl (Or.inl rfl)⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .LineTerminator, _, rfl, hdS, Or.inl (Or.inr (Or.inl rfl))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .Comment, _, rfl, hdS, Or.inl (Or.inr (Or.inr (Or.inl rfl)))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .CommonToken, _, rfl, hdS, Or.inr (Or.inl rfl)⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .RightBracePunctuator, _, rfl, hdS, Or.inr (Or.inr (Or.inl ⟨by decide, Or.inr (Or.inl rfl)⟩))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .RegularExpressionLiteral, _, rfl, hdS, Or.inr (Or.inr (Or.inl ⟨by decide, Or.inr (Or.inr rfl)⟩))⟩
      · rw [alts_fixed_eq alts_cert_core.2.2.2.2.1 alts_cert_core.2.2.2.2.2.1] at hsG
        simp only [srcsOf, writtenAlts, Gen.Lexical.InputElementRegExpOrTemplateTail, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsG
        rcases hsG with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .WhiteSpace, _, rfl, hdS, Or.inl (Or.inl rfl)⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .LineTerminator, _, rfl, hdS, Or.inl (Or.inr (Or.inl rfl))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .Comment, _, rfl, hdS, Or.inl (Or.inr (Or.inr (Or.inl rfl)))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .CommonToken, _, rfl, hdS, Or.inr (Or.inl rfl)⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .RegularExpressionLiteral, _, rfl, hdS, Or.inr (Or.inr (Or.inl ⟨by decide, Or.inr (Or.inr rfl)⟩))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .TemplateSubstitutionTail, _, rfl, hdS, Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))⟩
      · rw [alts_fixed_eq alts_cert_core.2.2.2.2.2.2.1 alts_cert_core.2.2.2.2.2.2.2.1] at hsG
        simp only [srcsOf, writtenAlts, Gen.Lexical.InputElementTemplateTail, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsG
        rcases hsG with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .WhiteSpace, _, rfl, hdS, Or.inl (Or.inl rfl)⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .LineTerminator, _, rfl, hdS, Or.inl (Or.inr (Or.inl rfl))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .Comment, _, rfl, hdS, Or.inl (Or.inr (Or.inr (Or.inl rfl)))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .CommonToken, _, rfl, hdS, Or.inr (Or.inl rfl)⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .DivPunctuator, _, rfl, hdS, Or.inr (Or.inr (Or.inl ⟨by decide, Or.inl rfl⟩))⟩
        · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .TemplateSubstitutionTail, _, rfl, hdS, Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩))⟩
      · rw [alts_lexical_eq] at hsG
        cases hhtml : Lex.html cx with
        | false =>
          simp only [hhtml, Bool.false_eq_true, ↓reduceIte, alts_cert_core.2.2.2.2.2.2.2.2.1,
            srcsOf, writtenAlts, Gen.Lexical.InputElementHashbangOrRegExp, List.zipIdx_cons, List.zipIdx_nil,
            List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsG
          rcases hsG with rfl | rfl | rfl | rfl | rfl | rfl
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .WhiteSpace, _, rfl, hdS, Or.inl (Or.inl rfl)⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .LineTerminator, _, rfl, hdS, Or.inl (Or.inr (Or.inl rfl))⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .Comment, _, rfl, hdS, Or.inl (Or.inr (Or.inr (Or.inl rfl)))⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .CommonToken, _, rfl, hdS, Or.inr (Or.inl rfl)⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .HashbangComment, _, rfl, hdS, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .RegularExpressionLiteral, _, rfl, hdS, Or.inr (Or.inr (Or.inl ⟨by decide, Or.inr (Or.inr rfl)⟩))⟩
        | true =>
          simp only [hhtml, ↓reduceIte, alts_cert_core.2.2.2.2.2.2.2.2.2,
            srcsOf, writtenAlts, Gen.Lexical.InputElementHashbangOrRegExp, List.zipIdx_cons, List.zipIdx_nil,
            List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hsG
          rcases hsG with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .WhiteSpace, _, rfl, hdS, Or.inl (Or.inl rfl)⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .LineTerminator, _, rfl, hdS, Or.inl (Or.inr (Or.inl rfl))⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .Comment, _, rfl, hdS, Or.inl (Or.inr (Or.inr (Or.inl rfl)))⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .CommonToken, _, rfl, hdS, Or.inr (Or.inl rfl)⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .HashbangComment, _, rfl, hdS, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .RegularExpressionLiteral, _, rfl, hdS, Or.inr (Or.inr (Or.inl ⟨by decide, Or.inr (Or.inr rfl)⟩))⟩
          · obtain ⟨dtS, rfl, rfl, hdS⟩ := seqWith_single_nt hswG; exact ⟨_, _, .HTMLCloseComment, _, rfl, hdS, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))⟩
  obtain ⟨idG, sG, sub, dtSub, rfl, hdSub, hkindOr⟩ := hchild
  have hkind : Element.kind ⟨a, b, g, (DTree.node g idG sG [] a b [] [dtSub]).toTree⟩ = some sub :=
    kind_of_plain_wrap hdSub
  have hhasEq := wrap_has_numLit (idG := idG) (sG := sG) (a := a) (b := b) (dtSub := dtSub) hgNeNum
  rcases hkindOr with hnonTok | htok
  · left
    have hnotAnc : numLitAncNTs.contains sub = false := by
      rcases hnonTok with rfl | rfl | rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
    have hhasF : (DTree.node g idG sG [] a b [] [dtSub]).toTree.has .NumericLiteral a b = false :=
      hhasEq.trans (plain_has_numLit_false hok a b (sizeOf dtSub) (Nat.le_refl _) hnotAnc hdSub)
    have hisTokF : Element.isToken ⟨a, b, g, (DTree.node g idG sG [] a b [] [dtSub]).toTree⟩ = false := by
      apply isToken_false_of_nonToken hkind
      rcases hnonTok with rfl | rfl | rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    refine ⟨hisTokF, hhasF, ?_⟩
    rcases hnonTok with rfl | rfl | rfl | ⟨hgEq, rfl⟩ | ⟨hgEq, hhtml, rfl⟩
    · exact Or.inl ⟨hkind, _, hdSub⟩
    · exact Or.inr (Or.inl ⟨hkind, _, hdSub⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hkind, _, hdSub⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hgEq, hkind, _, hdSub⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hgEq, hhtml, hkind, _, hdSub⟩)))
  · right
    rcases htok with rfl | ⟨hsubCls, hsubDirect⟩ | ⟨rfl, hgTail⟩
    · have hisTokT := isToken_true_of_tokKind hkind (Or.inl rfl)
      refine ⟨hisTokT, ?_⟩
      cases hdSub with
      | node sCT hsCT _ _ _ hswCT =>
        have hsCT := lex_mem_alts hok hsCT
        rw [haltsCT] at hsCT
        simp only [srcsOf, writtenAlts, Gen.Lexical.CommonToken, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsCT
        have hmemCom : ∀ c ∈ [NT.IdentifierName, .PrivateIdentifier, .Punctuator, .NumericLiteral,
            .StringLiteral, .NoSubstitutionTemplate, .TemplateHead], c ∈ Lex.classes g := by
          intro c hc; unfold Lex.classes; exact List.mem_append_left _ hc
        rcases hsCT with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨dtC, rfl, rfl, hdC⟩ := seqWith_single_nt hswCT
          exact ⟨.IdentifierName, hmemCom _ (by decide), _, hdC,
            hhasEq.trans ((wrap_has_numLit (by decide)).trans (tokClass_has_numLit hok (by decide) hdC))⟩
        · obtain ⟨dtC, rfl, rfl, hdC⟩ := seqWith_single_nt hswCT
          exact ⟨.PrivateIdentifier, hmemCom _ (by decide), _, hdC,
            hhasEq.trans ((wrap_has_numLit (by decide)).trans (tokClass_has_numLit hok (by decide) hdC))⟩
        · obtain ⟨dtC, rfl, rfl, hdC⟩ := seqWith_single_nt hswCT
          exact ⟨.Punctuator, hmemCom _ (by decide), _, hdC,
            hhasEq.trans ((wrap_has_numLit (by decide)).trans (tokClass_has_numLit hok (by decide) hdC))⟩
        · obtain ⟨dtC, rfl, rfl, hdC⟩ := seqWith_single_nt hswCT
          exact ⟨.NumericLiteral, hmemCom _ (by decide), _, hdC,
            hhasEq.trans ((wrap_has_numLit (by decide)).trans (tokClass_has_numLit hok (by decide) hdC))⟩
        · obtain ⟨dtC, rfl, rfl, hdC⟩ := seqWith_single_nt hswCT
          exact ⟨.StringLiteral, hmemCom _ (by decide), _, hdC,
            hhasEq.trans ((wrap_has_numLit (by decide)).trans (tokClass_has_numLit hok (by decide) hdC))⟩
        · obtain ⟨dtC, rfl, rfl, hdC⟩ := seqWith_single_nt hswCT
          cases hdC with
          | node sT hsT _ _ _ hswT =>
            have hsT := lex_mem_alts hok hsT
            rw [haltsTmpl] at hsT
            simp only [srcsOf, writtenAlts, Gen.Lexical.Template, List.zipIdx_cons, List.zipIdx_nil,
              List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsT
            rcases hsT with rfl | rfl
            · obtain ⟨dtT0, rfl, rfl, hdT0⟩ := seqWith_single_nt hswT
              exact ⟨.NoSubstitutionTemplate, hmemCom _ (by decide), _, hdT0,
                hhasEq.trans ((wrap_has_numLit (by decide)).trans
                  ((wrap_has_numLit (by decide)).trans (tokClass_has_numLit hok (by decide) hdT0)))⟩
            · obtain ⟨dtT0, rfl, rfl, hdT0⟩ := seqWith_single_nt hswT
              exact ⟨.TemplateHead, hmemCom _ (by decide), _, hdT0,
                hhasEq.trans ((wrap_has_numLit (by decide)).trans
                  ((wrap_has_numLit (by decide)).trans (tokClass_has_numLit hok (by decide) hdT0)))⟩
    · have hisTokT : Element.isToken ⟨a, b, g, (DTree.node g idG sG [] a b [] [dtSub]).toTree⟩ = true := by
        apply isToken_true_of_tokKind hkind
        rcases hsubDirect with rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      exact ⟨hisTokT, sub, hsubCls, dtSub, hdSub,
        hhasEq.trans (tokClass_has_numLit hok (classes_sub_allTokClasses g sub hsubCls) hdSub)⟩
    · have hisTokT := isToken_true_of_tokKind hkind (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      refine ⟨hisTokT, ?_⟩
      cases hdSub with
      | node sTl hsTl _ _ _ hswTl =>
        have hsTl := lex_mem_alts hok hsTl
        rw [haltsTail] at hsTl
        simp only [srcsOf, writtenAlts, Gen.Lexical.TemplateSubstitutionTail, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsTl
        have hmemTail : ∀ c ∈ [NT.TemplateMiddle, .TemplateTail], c ∈ Lex.classes g := by
          rcases hgTail with rfl | rfl <;> decide
        rcases hsTl with rfl | rfl
        · obtain ⟨dtT0, rfl, rfl, hdT0⟩ := seqWith_single_nt hswTl
          exact ⟨.TemplateMiddle, hmemTail _ (by decide), _, hdT0,
            hhasEq.trans ((wrap_has_numLit (by decide)).trans (tokClass_has_numLit hok (by decide) hdT0))⟩
        · obtain ⟨dtT0, rfl, rfl, hdT0⟩ := seqWith_single_nt hswTl
          exact ⟨.TemplateTail, hmemTail _ (by decide), _, hdT0,
            hhasEq.trans ((wrap_has_numLit (by decide)).trans (tokClass_has_numLit hok (by decide) hdT0))⟩

/-! ### Single-step trivia (`stepTrivia`), `Lex.skip`, `Trivia`, and `ChainEls` -/

def stepTrivia (cs : Array Nat) (first : Bool) (cx : Ctx) (k : Nat) : Option (Nat × Bool) :=
  match cs[k]? with
  | none => none
  | some c => match Lex.htmlAt Engine.builder cs first cx k with
    | some (e, l) => some (e, l)
    | none =>
      if Lex.isWS Engine.builder c then some (k + 1, false)
      else if Lex.isLT c then some (k + 1, true)
      else Lex.comment cs first k

theorem skipFrom_succ (cs : Array Nat) (first : Bool) (cx : Ctx) (f k : Nat) (lt : Bool) :
    Lex.skipFrom Engine.builder cs first cx (f + 1) k lt =
      match stepTrivia cs first cx k with
      | some (e, l) => Lex.skipFrom Engine.builder cs first cx f e (lt || l)
      | none => (k, lt) := by
  conv => lhs; unfold Lex.skipFrom
  unfold stepTrivia
  rcases cs[k]? with _ | c
  · rfl
  · dsimp only
    rcases Lex.htmlAt Engine.builder cs first cx k with _ | ⟨e, l⟩
    · dsimp only
      cases Lex.isWS Engine.builder c with
      | true => simp
      | false =>
        cases Lex.isLT c with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rcases Lex.comment cs first k with _ | ⟨e, l⟩ <;> rfl
    · rfl

private theorem no_lt_range_breaks_false {cs : Array Nat} {a b : Nat} (hb : b ≤ cs.size)
    (hno : ∀ p, a ≤ p → p < b → ∃ ch, cs[p]? = some ch ∧ Lex.isLT ch = false) :
    (slice cs.toList a b).any lineTerminators.contains = false := by
  rw [slice_any_lt_eq_extract, Bool.eq_false_iff, ne_eq, extract_any_isLT_iff cs hb]
  rintro ⟨p, ch, hp1, hp2, hpGet, hpLt⟩
  obtain ⟨ch', hpGet', hpNoLt⟩ := hno p hp1 hp2
  rw [hpGet] at hpGet'; injection hpGet' with he; subst he; rw [hpLt] at hpNoLt; cases hpNoLt

private theorem has_lt_range_breaks_true {cs : Array Nat} {a b p ch : Nat} (hb : b ≤ cs.size)
    (hp1 : a ≤ p) (hp2 : p < b) (hpGet : cs[p]? = some ch) (hpLt : Lex.isLT ch = true) :
    (slice cs.toList a b).any lineTerminators.contains = true := by
  rw [slice_any_lt_eq_extract, extract_any_isLT_iff cs hb]
  exact ⟨p, ch, hp1, hp2, hpGet, hpLt⟩

private theorem htmlAt_lt_branch {cs : Array Nat} {k c : Nat}
    (hc : cs[k]? = some c) (hne3c : c ≠ 0x3C) (hne2f : c ≠ 0x2F) :
    (match cs[k]?, cs[k + 1]?, cs[k + 2]?, cs[k + 3]? with
     | some 0x3C, some 0x21, some 0x2D, some 0x2D => some (Lex.lineEnd cs (k + 4), false)
     | some 0x2F, some 0x2A, _, _ => (Lex.closeAt cs (k + 2)).bind fun c =>
       if (cs.extract (k + 2) c).any Lex.isLT then (Lex.htmlClose Engine.builder cs (c + 2)).map (·, true) else none
     | some c, n, _, _ =>
       if Lex.isLT c then (Lex.htmlClose Engine.builder cs (if c == 0xD && n == some 0xA then k + 2 else k + 1)).map (·, true) else none
     | none, _, _, _ => none) =
    (if Lex.isLT c then (Lex.htmlClose Engine.builder cs (if c == 0xD && cs[k + 1]? == some 0xA then k + 2 else k + 1)).map (·, true) else none) := by
  rw [hc]
  rcases cs[k + 1]? with _ | c1
  · simp
  · by_cases h1 : c1 = 0x21
    · subst h1
      rcases cs[k + 2]? with _ | c2
      · simp
      · by_cases h2 : c2 = 0x2D
        · subst h2
          rcases cs[k + 3]? with _ | c3
          · simp
          · by_cases h3 : c3 = 0x2D
            · subst h3; simp [hne3c]
            · simp [h3]
        · simp [h2]
    · by_cases h1a : c1 = 0x2A
      · subst h1a; simp [hne2f]
      · simp [h1, h1a]

theorem stepTrivia_some_spec (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {k m : Nat} {l : Bool}
    (hst : stepTrivia cs first cx k = some (m, l)) :
    k < m ∧ m ≤ cs.size ∧
    (∃ e, TriviaElem Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first k m e ∧
      e.breaks cs.toList = l ∧ e.tree.has .NumericLiteral k m = false) ∧
    (∀ m' e', TriviaElem Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first k m' e' →
      m' = m ∧ e'.breaks cs.toList = l) := by
  let g0 : NT := if first && k == 0 then .InputElementHashbangOrRegExp else .InputElementDiv
  have hg0 : isLexGoal g0 = true := by
    dsimp only [g0]; split <;> decide
  have hkSz : k < cs.size := by
    unfold stepTrivia at hst
    rcases hg : cs[k]? with _ | c
    · rw [hg] at hst; cases hst
    · exact (Array.getElem?_eq_some_iff.mp hg).1
  have hkLe : k ≤ cs.size := Nat.le_of_lt hkSz
  -- Helper packaging a proved sub-kind + upper bound on all derivations of `g0`:
  have finish : ∀ (sub : NT) (dtSub : DTree),
      k < m → m ≤ cs.size →
      (sub = .WhiteSpace ∨ sub = .LineTerminator ∨ sub = .Comment ∨
       (g0 = .InputElementHashbangOrRegExp ∧ sub = .HashbangComment) ∨
       (g0 = .InputElementHashbangOrRegExp ∧ Lex.html cx = true ∧ sub = .HTMLCloseComment)) →
      (lexSpec cs cx).PlainDerives sub [] k m dtSub →
      (∀ h tree, k < h → h ≤ cs.size → LexDerives cx cs g0 [] k h tree →
        h ≤ m ∧ (h = m → Element.isToken ⟨k, m, g0, tree⟩ = false → Element.kind ⟨k, m, g0, tree⟩ = some sub)) →
      ((sub == .LineTerminator || (sub == .Comment && (slice cs.toList k m).any lineTerminators.contains)) = l) →
      k < m ∧ m ≤ cs.size ∧
      (∃ e, TriviaElem Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first k m e ∧
        e.breaks cs.toList = l ∧ e.tree.has .NumericLiteral k m = false) ∧
      (∀ m' e', TriviaElem Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first k m' e' →
        m' = m ∧ e'.breaks cs.toList = l) := by
    intro sub dtSub hkm hmSz hsubKind hdSub hub hbrEq
    obtain ⟨tree0, hder0, hkind0, hisTok0, hhas0⟩ := packNonToken hok hg0 hkLe hsubKind hdSub
    have hmax0 : ∀ h, m < h → h ≤ cs.toList.length → ¬ ∃ t, LexDerives cx cs g0 [] k h t := by
      intro h hmh hhLen ⟨t, hdt⟩
      have hhSz : h ≤ cs.size := by simpa using hhLen
      have ⟨hle, _⟩ := hub h t (by omega) hhSz hdt
      omega
    let e0 : Element := ⟨k, m, g0, tree0⟩
    have hte0 : TriviaElem Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first k m e0 :=
      ⟨hkm, by simpa using hmSz, rfl, rfl, by simp [e0, hisTok0], rfl, hder0, hmax0⟩
    have hbr0 : e0.breaks cs.toList = l := by
      unfold Element.breaks
      change (e0.kind == some .LineTerminator || e0.kind == some .Comment && (slice cs.toList k m).any lineTerminators.contains) = l
      rw [hkind0]
      simpa using hbrEq
    refine ⟨hkm, hmSz, ⟨e0, hte0, hbr0, hhas0⟩, fun m' e' hte' => ?_⟩
    rcases e' with ⟨ei, ej, eg, et⟩
    obtain ⟨hkm', hm'Len, hei, hej, hnotTok', hegoal, hder', hmax'⟩ := hte'
    dsimp only at hei hej hegoal hnotTok' hder' hmax'
    cases hei; cases hej
    have hegEq : eg = g0 := hegoal
    cases hegEq
    have hm'Sz : m' ≤ cs.size := by simpa using hm'Len
    have hle1 : m' ≤ m := (hub m' et hkm' hm'Sz hder').1
    have hle2 : m ≤ m' := by
      apply Classical.byContradiction; intro hgt
      exact hmax' m (by omega) (by simpa using hmSz) ⟨tree0, hder0⟩
    have hmEq : m' = m := by omega
    cases hmEq
    have hisTokF' : Element.isToken ⟨k, m, g0, et⟩ = false := Bool.eq_false_iff.mpr (by simpa using hnotTok')
    have hkind' := (hub m et hkm hmSz hder').2 rfl hisTokF'
    refine ⟨rfl, ?_⟩
    unfold Element.breaks
    rw [hkind']
    simpa using hbrEq
  unfold stepTrivia at hst
  rcases hck : cs[k]? with _ | c
  · rw [hck] at hst; cases hst
  · rw [hck] at hst; dsimp only at hst
    rcases hhtmlAt : Lex.htmlAt Engine.builder cs first cx k with _ | ⟨e, l0⟩
    · -- `htmlAt = none`
      rw [hhtmlAt] at hst; dsimp only at hst
      have hnoOpen1 : first = true → k = 0 → Lex.html cx = true → Lex.htmlClose Engine.builder cs 0 = none := by
        intro hf hk0 hht
        unfold Lex.htmlAt at hhtmlAt
        simp only [hht, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hf, hk0, beq_self_eq_true, Bool.and_self] at hhtmlAt
        cases hhc : Lex.htmlClose Engine.builder cs 0 with
        | none => rfl
        | some v => simp [hhc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hhtmlAt
      by_cases hws : Lex.isWS Engine.builder c = true
      · simp only [hws, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl⟩ := hst
        obtain ⟨dtWS, hdWS⟩ := (whiteSpace_iff hok).mpr ⟨c, hck, hws, rfl⟩
        have hnlt : Lex.isLT c = false := isWS_not_idStart hws ▸ isWS_not_isLT hws
        obtain ⟨hne2f, _, hne23, hne3c, _⟩ := isWS_ne hws
        apply finish .WhiteSpace dtWS (by omega) hkSz (Or.inl rfl) hdWS _ rfl
        intro h tree hkh hhSz hder
        rcases unpackInputElement hok hg0 hhSz hder with ⟨_, _, hnt⟩ | ⟨_, cls, hcls, dt, hd, _⟩
        · rcases hnt with ⟨hk, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨hgEq, hht, _, dtHC, hd⟩
          · obtain ⟨_, _, _, rfl⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩; exact ⟨Nat.le_refl _, fun _ _ => hk⟩
          · obtain ⟨c', hc', hlt', _⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩
            rw [hck] at hc'; injection hc' with he; subst he; rw [isWS_not_isLT hws] at hlt'; cases hlt'
          · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨hg0', _⟩ | ⟨hg0', _⟩ | ⟨_, hg0', _⟩ | ⟨_, c', hc', hlt', _⟩
            · exact absurd (Option.some.inj (hck.symm.trans hg0')) hne2f
            · exact absurd (Option.some.inj (hck.symm.trans hg0')) hne2f
            · exact absurd (Option.some.inj (hck.symm.trans hg0')) hne3c
            · rw [hck] at hc'; injection hc' with he; subst he; rw [isWS_not_isLT hws] at hlt'; cases hlt'
          · obtain ⟨hg0', _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩
            exact absurd (Option.some.inj (hck.symm.trans hg0')) hne23
          · have hfk : first = true ∧ k = 0 := by
              dsimp only [g0] at hgEq
              by_cases hif : (first && k == 0) = true
              · simpa [Bool.and_eq_true, beq_iff_eq] using hif
              · simp [hif] at hgEq
            rw [hfk.2] at hd
            exact absurd hd ((htmlClose_spec hok hcp hht 0).2 (hnoOpen1 hfk.1 hfk.2 hht) h dtHC)
        · obtain ⟨_, ⟨c', hc', hnws, _⟩, _⟩ := tokLead_props hok (sizeOf dt) (Nat.le_refl _)
            (List.mem_append_left _ (classes_sub_allTokClasses g0 cls hcls)) hkLe hd
          rw [hck] at hc'; injection hc' with he; subst he; rw [hws] at hnws; cases hnws
      · simp only [hws, Bool.false_eq_true, ↓reduceIte] at hst
        by_cases hlt : Lex.isLT c = true
        · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl⟩ := hst
          obtain ⟨dtLT, hdLT⟩ := (lineTerminator_iff hok).mpr ⟨c, hck, hlt, rfl⟩
          obtain ⟨hne2f, _, _, hne23, hne3c, _⟩ := isLT_ne hlt
          have hnoAfterLT : Lex.html cx = true →
              Lex.htmlClose Engine.builder cs (if c == 0xD && cs[k + 1]? == some 0xA then k + 2 else k + 1) = none := by
            intro hht
            unfold Lex.htmlAt at hhtmlAt
            simp only [hht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hhtmlAt
            have hnone2 : (match cs[k]?, cs[k + 1]?, cs[k + 2]?, cs[k + 3]? with
              | some 0x3C, some 0x21, some 0x2D, some 0x2D => some (Lex.lineEnd cs (k + 4), false)
              | some 0x2F, some 0x2A, _, _ => (Lex.closeAt cs (k + 2)).bind fun c =>
                if (cs.extract (k + 2) c).any Lex.isLT then (Lex.htmlClose Engine.builder cs (c + 2)).map (·, true) else none
              | some c, n, _, _ =>
                if Lex.isLT c then (Lex.htmlClose Engine.builder cs (if c == 0xD && n == some 0xA then k + 2 else k + 1)).map (·, true) else none
              | none, _, _, _ => none) = none := by
              cases h1 : (if first && k == 0 then (Lex.htmlClose Engine.builder cs 0).map (·, false) else none) with
              | none =>
                rw [h1] at hhtmlAt
                dsimp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hhtmlAt
                exact hhtmlAt
              | some _ => rw [h1] at hhtmlAt; simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hhtmlAt
            rw [htmlAt_lt_branch hck hne3c hne2f] at hnone2
            simp only [hlt, ↓reduceIte, Option.map_eq_none_iff] at hnone2
            exact hnone2
          apply finish .LineTerminator dtLT (by omega) hkSz (Or.inr (Or.inl rfl)) hdLT _ rfl
          intro h tree hkh hhSz hder
          rcases unpackInputElement hok hg0 hhSz hder with ⟨_, _, hnt⟩ | ⟨_, cls, hcls, dt, hd, _⟩
          · rcases hnt with ⟨_, _, hd⟩ | ⟨hk, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨hgEq, hht, _, dtHC, hd⟩
            · obtain ⟨c', hc', hws', _⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩
              rw [hck] at hc'; injection hc' with he; subst he; exact absurd hws' hws
            · obtain ⟨_, _, _, rfl⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩; exact ⟨Nat.le_refl _, fun _ _ => hk⟩
            · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨hg0', _⟩ | ⟨hg0', _⟩ | ⟨_, hg0', _⟩ | ⟨hht, c', hc', _, dtHC, hdHC⟩
              · exact absurd (Option.some.inj (hck.symm.trans hg0')) hne2f
              · exact absurd (Option.some.inj (hck.symm.trans hg0')) hne2f
              · exact absurd (Option.some.inj (hck.symm.trans hg0')) hne3c
              · rw [hck] at hc'; injection hc' with he; subst he
                exact absurd hdHC ((htmlClose_spec hok hcp hht _).2 (hnoAfterLT hht) h dtHC)
            · obtain ⟨hg0', _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩
              exact absurd (Option.some.inj (hck.symm.trans hg0')) hne23
            · have hfk : first = true ∧ k = 0 := by
                dsimp only [g0] at hgEq
                by_cases hif : (first && k == 0) = true
                · simpa [Bool.and_eq_true, beq_iff_eq] using hif
                · simp [hif] at hgEq
              rw [hfk.2] at hd
              exact absurd hd ((htmlClose_spec hok hcp hht 0).2 (hnoOpen1 hfk.1 hfk.2 hht) h dtHC)
          · obtain ⟨_, ⟨c', hc', _, hnlt⟩, _⟩ := tokLead_props hok (sizeOf dt) (Nat.le_refl _)
              (List.mem_append_left _ (classes_sub_allTokClasses g0 cls hcls)) hkLe hd
            rw [hck] at hc'; injection hc' with he; subst he; rw [hlt] at hnlt; cases hnlt
        · -- `htmlAt = none`, `isWS = false`, `isLT = false`, `Lex.comment cs first k = some (m, l)`
          simp only [hlt, Bool.false_eq_true, ↓reduceIte] at hst
          unfold Lex.comment at hst
          rw [hck] at hst
          rcases hck1 : cs[k + 1]? with _ | c1
          · rw [hck1] at hst
            by_cases hc1 : c = 0x2F
            · subst hc1; cases hst
            · by_cases hc2 : c = 0x23
              · subst hc2; cases hst
              · simp at hst
          · rw [hck1] at hst
            by_cases h2f : c = 0x2F
            · subst h2f
              by_cases h2f1 : c1 = 0x2F
              · -- `//` single-line comment
                subst h2f1
                simp only [Option.some.injEq, Prod.mk.injEq] at hst
                obtain ⟨rfl, rfl⟩ := hst
                have hk2Sz : k + 2 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hck1).1; omega
                have ⟨_, hleSz, hleNo, _⟩ := lineEnd_spec cs (k + 2)
                have hk2Le := lineEnd_ge_of_le cs hk2Sz
                obtain ⟨dtC, hdC⟩ := (comment_iff hok hcp).mpr (Or.inl ⟨hck, hck1, hk2Le, Nat.le_refl _⟩)
                have hnoBr : (slice cs.toList k (Lex.lineEnd cs (k + 2))).any lineTerminators.contains = false := by
                  apply no_lt_range_breaks_false hleSz
                  intro p hp1 hp2
                  by_cases hp0 : p = k
                  · subst hp0; exact ⟨0x2F, hck, rfl⟩
                  · by_cases hp1' : p = k + 1
                    · subst hp1'; exact ⟨0x2F, hck1, rfl⟩
                    · exact hleNo p (by omega) hp2
                apply finish .Comment dtC (by omega) hleSz (Or.inr (Or.inr (Or.inl rfl))) hdC _ (by simp [hnoBr])
                intro h tree hkh hhSz hder
                rcases unpackInputElement hok hg0 hhSz hder with ⟨_, _, hnt⟩ | ⟨_, cls, hcls, dt, hd, _⟩
                · rcases hnt with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨hk, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨hgEq, hht, _, dtHC, hd⟩
                  · obtain ⟨c', hc', hws', _⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩
                    rw [hck] at hc'; injection hc' with he; subst he; exact absurd hws' hws
                  · obtain ⟨c', hc', hlt', _⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩
                    rw [hck] at hc'; injection hc' with he; subst he; exact absurd hlt' hlt
                  · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨_, _, _, hjLe⟩ | ⟨_, hg1', _⟩ | ⟨_, hg0', _⟩ | ⟨_, c', hc', hlt', _⟩
                    · exact ⟨hjLe, fun _ _ => hk⟩
                    · rw [hck1] at hg1'; cases hg1'
                    · rw [hck] at hg0'; cases hg0'
                    · rw [hck] at hc'; injection hc' with he; subst he; cases hlt'
                  · obtain ⟨hg0', _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩; rw [hck] at hg0'; cases hg0'
                  · have hfk : first = true ∧ k = 0 := by
                      dsimp only [g0] at hgEq
                      by_cases hif : (first && k == 0) = true
                      · simpa [Bool.and_eq_true, beq_iff_eq] using hif
                      · simp [hif] at hgEq
                    rw [hfk.2] at hd
                    exact absurd hd ((htmlClose_spec hok hcp hht 0).2 (hnoOpen1 hfk.1 hfk.2 hht) h dtHC)
                · have ⟨_, _, _, _, _, hslash, _⟩ := tokLead_props hok (sizeOf dt) (Nat.le_refl _)
                    (List.mem_append_left _ (classes_sub_allTokClasses g0 cls hcls)) hkLe hd
                  have hhEq := hslash hck (Or.inl hck1)
                  omega
              · by_cases h2a1 : c1 = 0x2A
                · -- `/*` multi-line comment (without trailing Annex B `-->`)
                  subst h2a1
                  rcases hcl : Lex.closeAt cs (k + 2) with _ | cClose
                  · simp [hcl] at hst
                  · simp only [hcl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
                    obtain ⟨rfl, rfl⟩ := hst
                    obtain ⟨hk2c, hc1Sz, hc0, hc1, _⟩ := closeAt_some_spec cs (k + 2) cClose hcl
                    obtain ⟨dtC, hdC⟩ := (comment_iff (cx := cx) hok hcp).mpr (Or.inr (Or.inl ⟨hck, hck1, cClose, hcl, Or.inl rfl⟩))
                    have hnoTrailHC : Lex.html cx = true → (cs.extract (k + 2) cClose).any Lex.isLT = true →
                        Lex.htmlClose Engine.builder cs (cClose + 2) = none := by
                      intro hht hanyT
                      unfold Lex.htmlAt at hhtmlAt
                      simp only [hht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hhtmlAt
                      have hnone2 : (match cs[k]?, cs[k + 1]?, cs[k + 2]?, cs[k + 3]? with
                        | some 0x3C, some 0x21, some 0x2D, some 0x2D => some (Lex.lineEnd cs (k + 4), false)
                        | some 0x2F, some 0x2A, _, _ => (Lex.closeAt cs (k + 2)).bind fun c =>
                          if (cs.extract (k + 2) c).any Lex.isLT then (Lex.htmlClose Engine.builder cs (c + 2)).map (·, true) else none
                        | some c, n, _, _ =>
                          if Lex.isLT c then (Lex.htmlClose Engine.builder cs (if c == 0xD && n == some 0xA then k + 2 else k + 1)).map (·, true) else none
                        | none, _, _, _ => none) = none := by
                        cases h1 : (if first && k == 0 then (Lex.htmlClose Engine.builder cs 0).map (·, false) else none) with
                        | none =>
                          rw [h1] at hhtmlAt
                          dsimp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hhtmlAt
                          exact hhtmlAt
                        | some _ => rw [h1] at hhtmlAt; simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hhtmlAt
                      rw [hck, hck1] at hnone2
                      rw [hcl, Option.bind_some] at hnone2
                      simp only [hanyT, ↓reduceIte, Option.map_eq_none_iff] at hnone2
                      exact hnone2
                    have hbrEq : (slice cs.toList k (cClose + 2)).any lineTerminators.contains =
                        (cs.extract (k + 2) cClose).any Lex.isLT := by
                      rw [slice_any_lt_eq_extract]
                      apply Bool.eq_iff_iff.mpr
                      rw [extract_any_isLT_iff cs (by omega), extract_any_isLT_iff cs (by omega)]
                      constructor
                      · rintro ⟨p, ch, hp1, hp2, hpGet, hpLt⟩
                        by_cases hp0 : p = k
                        · subst hp0; rw [hck] at hpGet; injection hpGet with he; subst he; cases hpLt
                        · by_cases hp1' : p = k + 1
                          · subst hp1'; rw [hck1] at hpGet; injection hpGet with he; subst he; cases hpLt
                          · by_cases hpc : p = cClose
                            · subst hpc; rw [hc0] at hpGet; injection hpGet with he; subst he; cases hpLt
                            · by_cases hpc1 : p = cClose + 1
                              · subst hpc1; rw [hc1] at hpGet; injection hpGet with he; subst he; cases hpLt
                              · exact ⟨p, ch, by omega, by omega, hpGet, hpLt⟩
                      · rintro ⟨p, ch, hp1, hp2, hpGet, hpLt⟩
                        exact ⟨p, ch, by omega, by omega, hpGet, hpLt⟩
                    apply finish .Comment dtC (by omega) (by omega) (Or.inr (Or.inr (Or.inl rfl))) hdC _ (by simp [hbrEq])
                    intro h tree hkh hhSz hder
                    rcases unpackInputElement hok hg0 hhSz hder with ⟨_, _, hnt⟩ | ⟨_, cls, hcls, dt, hd, _⟩
                    · rcases hnt with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨hk, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨hgEq, hht, _, dtHC, hd⟩
                      · obtain ⟨c', hc', hws', _⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩
                        rw [hck] at hc'; injection hc' with he; subst he; exact absurd hws' hws
                      · obtain ⟨c', hc', hlt', _⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩
                        rw [hck] at hc'; injection hc' with he; subst he; exact absurd hlt' hlt
                      · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨_, hg1', _⟩ | ⟨_, _, c', hcl', hjOr⟩ | ⟨_, hg0', _⟩ | ⟨_, c', hc', hlt', _⟩
                        · rw [hck1] at hg1'; cases hg1'
                        · have hceq : c' = cClose := Option.some.inj (hcl'.symm.trans hcl); subst hceq
                          rcases hjOr with rfl | ⟨hht, hanyT, dtHC, hdHC⟩
                          · exact ⟨Nat.le_refl _, fun _ _ => hk⟩
                          · exact absurd hdHC ((htmlClose_spec hok hcp hht _).2 (hnoTrailHC hht hanyT) h dtHC)
                        · rw [hck] at hg0'; cases hg0'
                        · rw [hck] at hc'; injection hc' with he; subst he; cases hlt'
                      · obtain ⟨hg0', _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩; rw [hck] at hg0'; cases hg0'
                      · have hfk : first = true ∧ k = 0 := by
                          dsimp only [g0] at hgEq
                          by_cases hif : (first && k == 0) = true
                          · simpa [Bool.and_eq_true, beq_iff_eq] using hif
                          · simp [hif] at hgEq
                        rw [hfk.2] at hd
                        exact absurd hd ((htmlClose_spec hok hcp hht 0).2 (hnoOpen1 hfk.1 hfk.2 hht) h dtHC)
                    · have ⟨_, _, _, _, _, hslash, _⟩ := tokLead_props hok (sizeOf dt) (Nat.le_refl _)
                        (List.mem_append_left _ (classes_sub_allTokClasses g0 cls hcls)) hkLe hd
                      have hhEq := hslash hck (Or.inr hck1)
                      omega
                · simp [h2f1, h2a1] at hst
            · by_cases h23 : c = 0x23 ∧ c1 = 0x21
              · -- `#!` hashbang comment at 0 with `first`
                rcases h23 with ⟨rfl, rfl⟩
                by_cases hfk : (first && k == 0) = true
                · simp only [hfk, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hst
                  obtain ⟨rfl, rfl⟩ := hst
                  have hfk' : first = true ∧ k = 0 := by simpa [Bool.and_eq_true, beq_iff_eq] using hfk
                  obtain ⟨hfEq, hkEq⟩ := hfk'
                  have hg0Eq : g0 = .InputElementHashbangOrRegExp := by dsimp only [g0]; rw [hfk]; rfl
                  have hk2Sz : k + 2 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hck1).1; omega
                  have ⟨_, hleSz, _, _⟩ := lineEnd_spec cs (k + 2)
                  have hk2Le := lineEnd_ge_of_le cs hk2Sz
                  obtain ⟨dtHB, hdHB⟩ := (hashbangComment_iff (cx := cx) hok hcp).mpr ⟨hck, hck1, hk2Le, Nat.le_refl _⟩
                  apply finish .HashbangComment dtHB (by omega) hleSz
                    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hg0Eq, rfl⟩)))) hdHB _ rfl
                  intro h tree hkh hhSz hder
                  rcases unpackInputElement hok hg0 hhSz hder with ⟨_, _, hnt⟩ | ⟨_, cls, hcls, dt, hd, _⟩
                  · rcases hnt with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, hk, _, hd⟩ | ⟨_, hht, _, dtHC, hd⟩
                    · obtain ⟨c', hc', hws', _⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩
                      rw [hck] at hc'; injection hc' with he; subst he; exact absurd hws' hws
                    · obtain ⟨c', hc', hlt', _⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩
                      rw [hck] at hc'; injection hc' with he; subst he; exact absurd hlt' hlt
                    · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨hg0', _⟩ | ⟨hg0', _⟩ | ⟨_, hg0', _⟩ | ⟨_, c', hc', hlt', _⟩
                      · rw [hck] at hg0'; cases hg0'
                      · rw [hck] at hg0'; cases hg0'
                      · rw [hck] at hg0'; cases hg0'
                      · rw [hck] at hc'; injection hc' with he; subst he; cases hlt'
                    · obtain ⟨_, _, _, hjLe⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩
                      exact ⟨hjLe, fun _ _ => hk⟩
                    · rw [hkEq] at hd
                      exact absurd hd ((htmlClose_spec hok hcp hht 0).2 (hnoOpen1 hfEq hkEq hht) h dtHC)
                  · have ⟨_, _, _, _, _, _, hhash, _⟩ := tokLead_props hok (sizeOf dt) (Nat.le_refl _)
                      (List.mem_append_left _ (classes_sub_allTokClasses g0 cls hcls)) hkLe hd
                    exact absurd hck1 (hhash hck)
                · simp [hfk] at hst
              · by_cases hc23 : c = 0x23
                · subst hc23; have hc1Ne : c1 ≠ 0x21 := fun h => h23 ⟨rfl, h⟩; simp [hc1Ne] at hst
                · simp [h2f, hc23] at hst
    · -- `htmlAt = some (e, l0)`
      rw [hhtmlAt] at hst
      injection hst with hpEq
      rcases Prod.mk.inj hpEq with ⟨heEq, hlEq⟩
      subst e; subst l0
      unfold Lex.htmlAt at hhtmlAt
      cases hht : Lex.html cx with
      | false => simp [hht] at hhtmlAt
      | true =>
        simp only [hht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hhtmlAt
        cases hopen1 : (if first && k == 0 then (Lex.htmlClose Engine.builder cs 0).map (·, false) else none) with
        | some pair0 =>
          rw [hopen1] at hhtmlAt
          simp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hhtmlAt
          subst hhtmlAt
          by_cases hfk : (first && k == 0) = true
          · simp only [hfk, ↓reduceIte] at hopen1
            obtain ⟨rfl, rfl⟩ : first = true ∧ k = 0 := by simpa [Bool.and_eq_true, beq_iff_eq] using hfk
            rcases hhc0 : Lex.htmlClose Engine.builder cs 0 with _ | e0
            · simp [hhc0] at hopen1
            · simp only [hhc0, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hopen1
              obtain ⟨rfl, rfl⟩ := hopen1
              obtain ⟨h3e, heSz, ⟨dtHC, hdHC⟩, hubHC⟩ := (htmlClose_spec hok hcp hht 0).1 e0 hhc0
              apply finish .HTMLCloseComment dtHC (by omega) heSz
                (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hht, rfl⟩)))) hdHC _ rfl
              intro h tree hkh hhSz hder
              have ⟨h0w, _, hwAll, _⟩ := wsEnd_spec cs 0
              unfold Lex.htmlClose at hhc0; dsimp only at hhc0
              -- First check what starts at 0 when `htmlClose 0 = some e0`:
              have hstart0 : (0 < Lex.wsEnd Engine.builder cs 0 ∧ Lex.isWS Engine.builder c = true) ∨
                  (Lex.wsEnd Engine.builder cs 0 = 0 ∧ cs[0]? = some 0x2D ∧ cs[1]? = some 0x2D ∧ cs[2]? = some 0x3E) ∨
                  (Lex.wsEnd Engine.builder cs 0 = 0 ∧ cs[0]? = some 0x2F ∧ cs[1]? = some 0x2A ∧
                    ∃ cCl, Lex.closeAt cs 2 = some cCl ∧ (cs.extract 2 cCl).any Lex.isLT = false ∧ cCl + 5 ≤ e0) := by
                by_cases hwpos : 0 < Lex.wsEnd Engine.builder cs 0
                · obtain ⟨c', hc', hws'⟩ := hwAll 0 (Nat.le_refl _) hwpos
                  rw [hck] at hc'; injection hc' with he; subst he
                  exact Or.inl ⟨hwpos, hws'⟩
                · have hw0 : Lex.wsEnd Engine.builder cs 0 = 0 := by omega
                  rw [hw0] at hhc0
                  simp only [Nat.zero_add] at hhc0
                  rcases hg0 : cs[0]? with _ | cw0; · rw [hg0] at hhc0; cases hhc0
                  rw [hg0] at hhc0
                  by_cases h2d : cw0 = 0x2D
                  · subst h2d
                    rcases hg1 : cs[1]? with _ | cw1; · rw [hg1] at hhc0; cases hhc0
                    rw [hg1] at hhc0
                    by_cases h2d1 : cw1 = 0x2D
                    · subst h2d1
                      rcases hg2 : cs[2]? with _ | cw2; · rw [hg2] at hhc0; cases hhc0
                      rw [hg2] at hhc0
                      by_cases h3e' : cw2 = 0x3E
                      · subst h3e'; exact Or.inr (Or.inl ⟨hw0, rfl, rfl, rfl⟩)
                      · simp [h3e'] at hhc0
                    · simp [h2d1] at hhc0
                  · by_cases h2f : cw0 = 0x2F
                    · subst h2f
                      rcases hg1 : cs[1]? with _ | cw1; · rw [hg1] at hhc0; cases hhc0
                      rw [hg1] at hhc0
                      by_cases h2a : cw1 = 0x2A
                      · subst h2a
                        rcases hcl : Lex.closeAt cs 2 with _ | cCl; · rw [hcl] at hhc0; cases hhc0
                        rw [hcl] at hhc0
                        dsimp only at hhc0
                        by_cases hanyLt : (cs.extract 2 cCl).any Lex.isLT = true
                        · rw [hanyLt] at hhc0; cases hhc0
                        · have hanyF : (cs.extract 2 cCl).any Lex.isLT = false := Bool.eq_false_iff.mpr hanyLt
                          rw [hanyF] at hhc0
                          simp only [Bool.false_eq_true, ↓reduceIte] at hhc0
                          by_cases hcond : 0 < cCl + 2 ∧ cCl + 2 ≤ cs.size
                          · simp only [hcond, and_self, ↓reduceDIte] at hhc0
                            have ⟨hc5, _⟩ := (htmlClose_spec hok hcp hht (cCl + 2)).1 e0 hhc0
                            exact Or.inr (Or.inr ⟨hw0, rfl, rfl, cCl, rfl, hanyF, by omega⟩)
                          · simp only [hcond, ↓reduceDIte] at hhc0; cases hhc0
                      · simp [h2a] at hhc0
                    · simp [h2d, h2f] at hhc0
              rcases unpackInputElement hok hg0 hhSz hder with ⟨_, _, hnt⟩ | ⟨_, cls, hcls, dt, hd, _⟩
              · rcases hnt with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨_, _, hk, _, hd⟩
                · obtain ⟨_, _, _, rfl⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩
                  exact ⟨by omega, fun hEq => by omega⟩
                · obtain ⟨_, _, _, rfl⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩
                  exact ⟨by omega, fun hEq => by omega⟩
                · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨hg0', hg1', _⟩ | ⟨hg0', hg1', c', hcl', hjOr⟩ | ⟨_, hg0', _⟩ | ⟨_, c', hc', hlt', _⟩
                  · rcases hstart0 with ⟨_, hws'⟩ | ⟨_, hd0, _⟩ | ⟨_, _, ha1, _⟩
                    · exact absurd (Option.some.inj (hck.symm.trans hg0')) (isWS_ne hws').1
                    · rw [hd0] at hg0'; cases hg0'
                    · rw [ha1] at hg1'; cases hg1'
                  · rcases hstart0 with ⟨_, hws'⟩ | ⟨_, hd0, _⟩ | ⟨_, _, _, cCl, hcl, hanyF, hc5⟩
                    · exact absurd (Option.some.inj (hck.symm.trans hg0')) (isWS_ne hws').1
                    · rw [hd0] at hg0'; cases hg0'
                    · have hceq : c' = cCl := Option.some.inj (hcl'.symm.trans hcl); subst hceq
                      rcases hjOr with rfl | ⟨_, hanyT, _⟩
                      · exact ⟨by omega, fun _ => by omega⟩
                      · rw [hanyF] at hanyT; cases hanyT
                  · rcases hstart0 with ⟨_, hws'⟩ | ⟨_, hd0, _⟩ | ⟨_, hf0, _⟩
                    · exact absurd (Option.some.inj (hck.symm.trans hg0')) (isWS_ne hws').2.2.2.1
                    · rw [hd0] at hg0'; cases hg0'
                    · rw [hf0] at hg0'; cases hg0'
                  · rcases hstart0 with ⟨_, hws'⟩ | ⟨_, hd0, _⟩ | ⟨_, hf0, _⟩
                    · rw [hck] at hc'; injection hc' with he; subst he; rw [isWS_not_isLT hws'] at hlt'; cases hlt'
                    · rw [hd0] at hc'; injection hc' with he; subst he; cases hlt'
                    · rw [hf0] at hc'; injection hc' with he; subst he; cases hlt'
                · obtain ⟨hg0', _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩
                  rcases hstart0 with ⟨_, hws'⟩ | ⟨_, hd0, _⟩ | ⟨_, hf0, _⟩
                  · exact absurd (Option.some.inj (hck.symm.trans hg0')) (isWS_ne hws').2.2.1
                  · rw [hd0] at hg0'; cases hg0'
                  · rw [hf0] at hg0'; cases hg0'
                · exact ⟨hubHC h _ hd, fun _ _ => hk⟩
              · have ⟨_, ⟨c', hc', hnws, _⟩, _, _, _, hslash, _, _, hdash⟩ := tokLead_props hok (sizeOf dt) (Nat.le_refl _)
                  (List.mem_append_left _ (classes_sub_allTokClasses g0 cls hcls)) hkLe hd
                rcases hstart0 with ⟨_, hws'⟩ | ⟨_, hd0, hd1, hd2⟩ | ⟨_, hf0, hf1, _⟩
                · rw [hck] at hc'; injection hc' with he; subst he; rw [hws'] at hnws; cases hnws
                · have := hdash hd0 hd1 hd2; omega
                · have := hslash hf0 (Or.inr hf1); omega
          · simp [hfk] at hopen1
        | none =>
          -- `open1 = none`, so `htmlAt` matched `<!--`, `/* ... \n ... */ -->`, or `LT -->`
          rw [hopen1] at hhtmlAt
          dsimp only [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hhtmlAt
          have hnoOpen1' : first = true → k = 0 → Lex.htmlClose Engine.builder cs 0 = none := by
            intro hf hk0; simp [hf, hk0] at hopen1; exact hopen1
          by_cases hc3c : c = 0x3C
          · subst hc3c
            rw [hck] at hhtmlAt
            have hex4 : cs[k + 1]? = some 0x21 ∧ cs[k + 2]? = some 0x2D ∧ cs[k + 3]? = some 0x2D ∧
                m = Lex.lineEnd cs (k + 4) ∧ l = false := by
              rcases hck1 : cs[k + 1]? with _ | c1
              · rw [hck1] at hhtmlAt; simp [Lex.isLT] at hhtmlAt
              · rw [hck1] at hhtmlAt
                by_cases h1 : c1 = 0x21
                · subst h1
                  rcases hck2 : cs[k + 2]? with _ | c2
                  · rw [hck2] at hhtmlAt; simp [Lex.isLT] at hhtmlAt
                  · rw [hck2] at hhtmlAt
                    by_cases h2 : c2 = 0x2D
                    · subst h2
                      rcases hck3 : cs[k + 3]? with _ | c3
                      · rw [hck3] at hhtmlAt; simp [Lex.isLT] at hhtmlAt
                      · rw [hck3] at hhtmlAt
                        by_cases h3 : c3 = 0x2D
                        · subst h3; simp at hhtmlAt; exact ⟨rfl, rfl, rfl, hhtmlAt.1.symm, hhtmlAt.2⟩
                        · simp [h3, Lex.isLT] at hhtmlAt
                    · simp [h2, Lex.isLT] at hhtmlAt
                · simp [h1, Lex.isLT] at hhtmlAt
            obtain ⟨hck1, hck2, hck3, rfl, rfl⟩ := hex4
            have hk4Sz : k + 4 ≤ cs.size := by have := (Array.getElem?_eq_some_iff.mp hck3).1; omega
            have ⟨_, hleSz, hleNo, _⟩ := lineEnd_spec cs (k + 4)
            have hk4Le := lineEnd_ge_of_le cs hk4Sz
            obtain ⟨dtC, hdC⟩ := (comment_iff hok hcp).mpr
              (Or.inr (Or.inr (Or.inl ⟨hht, hck, hck1, hck2, hck3, hk4Le, Nat.le_refl _⟩)))
            have hnoBr : (slice cs.toList k (Lex.lineEnd cs (k + 4))).any lineTerminators.contains = false := by
              apply no_lt_range_breaks_false hleSz
              intro p hp1 hp2
              by_cases hp0 : p = k; · subst hp0; exact ⟨0x3C, hck, rfl⟩
              by_cases hp1' : p = k + 1; · subst hp1'; exact ⟨0x21, hck1, rfl⟩
              by_cases hp2' : p = k + 2; · subst hp2'; exact ⟨0x2D, hck2, rfl⟩
              by_cases hp3' : p = k + 3; · subst hp3'; exact ⟨0x2D, hck3, rfl⟩
              exact hleNo p (by omega) hp2
            apply finish .Comment dtC (by omega) hleSz (Or.inr (Or.inr (Or.inl rfl))) hdC _ (by simp [hnoBr])
            intro h tree hkh hhSz hder
            rcases unpackInputElement hok hg0 hhSz hder with ⟨_, _, hnt⟩ | ⟨_, cls, hcls, dt, hd, _⟩
            · rcases hnt with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨hk, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨hgEq, _, _, dtHC, hd⟩
              · obtain ⟨c', hc', hws', _⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩
                exact absurd (Option.some.inj (hc'.symm.trans hck)) (isWS_ne hws').2.2.2.1
              · obtain ⟨c', hc', hlt', _⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩
                rw [hck] at hc'; injection hc' with he; subst he; cases hlt'
              · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨hg0', _⟩ | ⟨hg0', _⟩ | ⟨_, _, _, _, _, _, hjLe⟩ | ⟨_, c', hc', hlt', _⟩
                · rw [hck] at hg0'; cases hg0'
                · rw [hck] at hg0'; cases hg0'
                · exact ⟨hjLe, fun _ _ => hk⟩
                · rw [hck] at hc'; injection hc' with he; subst he; cases hlt'
              · obtain ⟨hg0', _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩; rw [hck] at hg0'; cases hg0'
              · have hfk : first = true ∧ k = 0 := by
                  dsimp only [g0] at hgEq
                  by_cases hif : (first && k == 0) = true
                  · simpa [Bool.and_eq_true, beq_iff_eq] using hif
                  · simp [hif] at hgEq
                rw [hfk.2] at hd
                exact absurd hd ((htmlClose_spec hok hcp hht 0).2 (hnoOpen1' hfk.1 hfk.2) h dtHC)
            · have ⟨_, _, _, _, _, _, _, hlt3c, _⟩ := tokLead_props hok (sizeOf dt) (Nat.le_refl _)
                (List.mem_append_left _ (classes_sub_allTokClasses g0 cls hcls)) hkLe hd
              have := hlt3c hck hck1; omega
          · by_cases hc2f : c = 0x2F
            · subst hc2f
              rw [hck] at hhtmlAt
              have hexML : cs[k + 1]? = some 0x2A ∧ ∃ cCl, Lex.closeAt cs (k + 2) = some cCl ∧
                  (cs.extract (k + 2) cCl).any Lex.isLT = true ∧
                  Lex.htmlClose Engine.builder cs (cCl + 2) = some m ∧ l = true := by
                rcases hck1 : cs[k + 1]? with _ | c1; · rw [hck1] at hhtmlAt; simp [Lex.isLT] at hhtmlAt
                rw [hck1] at hhtmlAt
                by_cases h2a : c1 = 0x2A
                · subst h2a
                  rcases hcl : Lex.closeAt cs (k + 2) with _ | cCl; · rw [hcl] at hhtmlAt; cases hhtmlAt
                  rw [hcl, Option.bind_some] at hhtmlAt
                  by_cases hany : (cs.extract (k + 2) cCl).any Lex.isLT = true
                  · rw [hany] at hhtmlAt; simp only [↓reduceIte] at hhtmlAt
                    rcases hhc : Lex.htmlClose Engine.builder cs (cCl + 2) with _ | e1; · simp [hhc] at hhtmlAt
                    simp only [hhc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hhtmlAt
                    exact ⟨rfl, cCl, rfl, hany, hhtmlAt.1 ▸ hhc, hhtmlAt.2.symm⟩
                  · have hanyF : (cs.extract (k + 2) cCl).any Lex.isLT = false := Bool.eq_false_iff.mpr hany
                    rw [hanyF] at hhtmlAt; cases hhtmlAt
                · simp [h2a, Lex.isLT] at hhtmlAt
              obtain ⟨hck1, cCl, hcl, hanyT, hhc, rfl⟩ := hexML
              obtain ⟨hk2c, _, _, _, _⟩ := closeAt_some_spec cs (k + 2) cCl hcl
              obtain ⟨hc5m, hmSz, ⟨dtHC, hdHC⟩, hubHC⟩ := (htmlClose_spec hok hcp hht (cCl + 2)).1 m hhc
              obtain ⟨dtC, hdC⟩ := (comment_iff hok hcp).mpr
                (Or.inr (Or.inl ⟨hck, hck1, cCl, hcl, Or.inr ⟨hht, hanyT, dtHC, hdHC⟩⟩))
              obtain ⟨pLt, chLt, hp1, hp2, hpGet, hpIsLt⟩ := (extract_any_isLT_iff cs (by omega)).mp hanyT
              have hbrT := has_lt_range_breaks_true hmSz (a := k) (by omega) (by omega) hpGet hpIsLt
              apply finish .Comment dtC (by omega) hmSz (Or.inr (Or.inr (Or.inl rfl))) hdC _ (by simp [hbrT])
              intro h tree hkh hhSz hder
              rcases unpackInputElement hok hg0 hhSz hder with ⟨_, _, hnt⟩ | ⟨_, cls, hcls, dt, hd, _⟩
              · rcases hnt with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨hk, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨hgEq, _, _, dtHC', hd⟩
                · obtain ⟨c', hc', hws', _⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩
                  exact absurd (Option.some.inj (hc'.symm.trans hck)) (isWS_ne hws').1
                · obtain ⟨c', hc', hlt', _⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩
                  rw [hck] at hc'; injection hc' with he; subst he; cases hlt'
                · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨_, hg1', _⟩ | ⟨_, _, c', hcl', hjOr⟩ | ⟨_, hg0', _⟩ | ⟨_, c', hc', hlt', _⟩
                  · rw [hck1] at hg1'; cases hg1'
                  · have hceq : c' = cCl := Option.some.inj (hcl'.symm.trans hcl); subst hceq
                    rcases hjOr with rfl | ⟨_, _, dtHC'', hdHC''⟩
                    · exact ⟨by omega, fun _ => by omega⟩
                    · exact ⟨hubHC h dtHC'' hdHC'', fun _ _ => hk⟩
                  · rw [hck] at hg0'; cases hg0'
                  · rw [hck] at hc'; injection hc' with he; subst he; cases hlt'
                · obtain ⟨hg0', _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩; rw [hck] at hg0'; cases hg0'
                · have hfk : first = true ∧ k = 0 := by
                    dsimp only [g0] at hgEq
                    by_cases hif : (first && k == 0) = true
                    · simpa [Bool.and_eq_true, beq_iff_eq] using hif
                    · simp [hif] at hgEq
                  rw [hfk.2] at hd
                  exact absurd hd ((htmlClose_spec hok hcp hht 0).2 (hnoOpen1' hfk.1 hfk.2) h dtHC')
              · have ⟨_, _, _, _, _, hslash, _⟩ := tokLead_props hok (sizeOf dt) (Nat.le_refl _)
                  (List.mem_append_left _ (classes_sub_allTokClasses g0 cls hcls)) hkLe hd
                have := hslash hck (Or.inr hck1); omega
            · -- Neither `0x3C` nor `0x2F`, so `isLT c = true` + `htmlClose kAfterLT = some m`
              have hltBr : (if Lex.isLT c then (Lex.htmlClose Engine.builder cs (if c == 0xD && cs[k + 1]? == some 0xA then k + 2 else k + 1)).map (·, true) else none) = some (m, l) := by
                rw [hck] at hhtmlAt
                rcases hck1 : cs[k + 1]? with _ | c1
                · rw [hck1] at hhtmlAt; simpa using hhtmlAt
                · rw [hck1] at hhtmlAt
                  by_cases h1 : c1 = 0x21
                  · subst h1
                    rcases hck2 : cs[k + 2]? with _ | c2
                    · rw [hck2] at hhtmlAt; simpa using hhtmlAt
                    · rw [hck2] at hhtmlAt
                      by_cases h2 : c2 = 0x2D
                      · subst h2
                        rcases hck3 : cs[k + 3]? with _ | c3
                        · rw [hck3] at hhtmlAt; simpa using hhtmlAt
                        · rw [hck3] at hhtmlAt
                          by_cases h3 : c3 = 0x2D
                          · subst h3; simpa [hc3c] using hhtmlAt
                          · simpa [h3] using hhtmlAt
                      · simpa [h2] using hhtmlAt
                  · by_cases h1a : c1 = 0x2A
                    · subst h1a; simpa [hc2f] using hhtmlAt
                    · simpa [h1, h1a] using hhtmlAt
              clear hhtmlAt; rename_i _ ; have hhtmlAt := hltBr
              by_cases hlt : Lex.isLT c = true
              · simp only [hlt, ↓reduceIte] at hhtmlAt
                let kNext := if c == 0xD && cs[k + 1]? == some 0xA then k + 2 else k + 1
                change (Lex.htmlClose Engine.builder cs kNext).map (·, true) = some (m, l) at hhtmlAt
                rcases hhc : Lex.htmlClose Engine.builder cs kNext with _ | e1; · simp [hhc] at hhtmlAt
                simp only [hhc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hhtmlAt
                obtain ⟨rfl, rfl⟩ := hhtmlAt
                have hkLtNext : k + 1 ≤ kNext := by dsimp only [kNext]; split <;> omega
                obtain ⟨hnext3, hmSz, ⟨dtHC, hdHC⟩, hubHC⟩ := (htmlClose_spec hok hcp hht kNext).1 e1 hhc
                obtain ⟨dtC, hdC⟩ := (comment_iff hok hcp).mpr
                  (Or.inr (Or.inr (Or.inr ⟨hht, c, hck, hlt, dtHC, hdHC⟩)))
                have hbrT := has_lt_range_breaks_true hmSz (a := k) (Nat.le_refl _) (by omega) hck hlt
                obtain ⟨hne2f, _, _, hne23, hne3c, _⟩ := isLT_ne hlt
                apply finish .Comment dtC (by omega) hmSz (Or.inr (Or.inr (Or.inl rfl))) hdC _ (by simp [hbrT])
                intro h tree hkh hhSz hder
                rcases unpackInputElement hok hg0 hhSz hder with ⟨_, _, hnt⟩ | ⟨_, cls, hcls, dt, hd, _⟩
                · rcases hnt with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨hk, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨hgEq, _, _, dtHC', hd⟩
                  · obtain ⟨c', hc', hws', _⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩
                    rw [hck] at hc'; injection hc' with he; subst he
                    rw [isWS_not_isLT hws'] at hlt; cases hlt
                  · obtain ⟨_, _, _, rfl⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩
                    exact ⟨by omega, fun _ => by omega⟩
                  · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨hg0', _⟩ | ⟨hg0', _⟩ | ⟨_, hg0', _⟩ | ⟨_, c', hc', _, dtHC'', hdHC''⟩
                    · exact absurd (Option.some.inj (hck.symm.trans hg0')) hne2f
                    · exact absurd (Option.some.inj (hck.symm.trans hg0')) hne2f
                    · exact absurd (Option.some.inj (hck.symm.trans hg0')) hne3c
                    · rw [hck] at hc'; injection hc' with he; subst he
                      exact ⟨hubHC h dtHC'' hdHC'', fun _ _ => hk⟩
                  · obtain ⟨hg0', _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩
                    exact absurd (Option.some.inj (hck.symm.trans hg0')) hne23
                  · have hfk : first = true ∧ k = 0 := by
                      dsimp only [g0] at hgEq
                      by_cases hif : (first && k == 0) = true
                      · simpa [Bool.and_eq_true, beq_iff_eq] using hif
                      · simp [hif] at hgEq
                    rw [hfk.2] at hd
                    exact absurd hd ((htmlClose_spec hok hcp hht 0).2 (hnoOpen1' hfk.1 hfk.2) h dtHC')
                · obtain ⟨_, ⟨c', hc', _, hnlt⟩, _⟩ := tokLead_props hok (sizeOf dt) (Nat.le_refl _)
                    (List.mem_append_left _ (classes_sub_allTokClasses g0 cls hcls)) hkLe hd
                  rw [hck] at hc'; injection hc' with he; subst he; rw [hlt] at hnlt; cases hnlt
              · simp [hlt] at hhtmlAt

theorem stepTrivia_none_no_nontoken (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {k : Nat}
    (hst : stepTrivia cs first cx k = none)
    {g : NT} (hg : isLexGoal g = true) (hgb : g = .InputElementHashbangOrRegExp → first = true ∧ k = 0)
    {j : Nat} (hj : j ≤ cs.size) {tree : Tree}
    (hd : LexDerives cx cs g [] k j tree) :
    Element.isToken ⟨k, j, g, tree⟩ = true := by
  rcases unpackInputElement hok hg hj hd with ⟨_, _, hnt⟩ | ⟨hisTok, _⟩
  · exfalso
    unfold stepTrivia at hst
    rcases hck : cs[k]? with _ | c
    · rcases hnt with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, _, hd⟩ | ⟨hgEq, hht, _, dtHC, hd⟩
      · obtain ⟨_, hc, _⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩; rw [hck] at hc; cases hc
      · obtain ⟨_, hc, _⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩; rw [hck] at hc; cases hc
      · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨hc, _⟩ | ⟨hc, _⟩ | ⟨_, hc, _⟩ | ⟨_, _, hc, _⟩ <;> (rw [hck] at hc; cases hc)
      · obtain ⟨hc, _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩; rw [hck] at hc; cases hc
      · obtain ⟨rfl, rfl⟩ := hgb hgEq
        rcases hhc : Lex.htmlClose Engine.builder cs 0 with _ | e0
        · exact absurd hd ((htmlClose_spec hok hcp hht 0).2 hhc j dtHC)
        · have ⟨h3, _, _, hub⟩ := (htmlClose_spec hok hcp hht 0).1 e0 hhc
          have hkSz : cs.size ≤ 0 := Array.getElem?_eq_none_iff.mp hck
          have ⟨_, hjSz, _⟩ := lexPlain_to_derives hok (Nat.zero_le _) hd
          have := hub j dtHC hd
          -- wait: if `cs.size ≤ 0`, `e0 ≤ cs.size` and `3 ≤ e0` gives immediate contradiction!
          have ⟨_, he0Sz, _⟩ := (htmlClose_spec hok hcp hht 0).1 e0 hhc
          omega
    · rw [hck] at hst; dsimp only at hst
      rcases hhtmlAt : Lex.htmlAt Engine.builder cs first cx k with _ | ⟨e, l⟩
      · rw [hhtmlAt] at hst; dsimp only at hst
        cases hws : Lex.isWS Engine.builder c with
        | true => rw [hws] at hst; simp at hst
        | false =>
          rw [hws] at hst; simp only [Bool.false_eq_true, ↓reduceIte] at hst
          cases hlt : Lex.isLT c with
          | true => rw [hlt] at hst; simp at hst
          | false =>
            rw [hlt] at hst; simp only [Bool.false_eq_true, ↓reduceIte] at hst
            -- `hst : Lex.comment cs first k = none`
            rcases hnt with ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨_, _, hd⟩ | ⟨hgEq, _, _, hd⟩ | ⟨hgEq, hht, _, dtHC, hd⟩
            · obtain ⟨c', hc', hws', _⟩ := (whiteSpace_iff hok).mp ⟨_, hd⟩
              rw [hck] at hc'; injection hc' with he; subst he; rw [hws] at hws'; cases hws'
            · obtain ⟨c', hc', hlt', _⟩ := (lineTerminator_iff hok).mp ⟨_, hd⟩
              rw [hck] at hc'; injection hc' with he; subst he; rw [hlt] at hlt'; cases hlt'
            · rcases (comment_iff hok hcp).mp ⟨_, hd⟩ with ⟨hg0, hg1, _⟩ | ⟨hg0, hg1, cCl, hcl, _⟩ | ⟨hht, hg0, hg1, hg2, hg3, _⟩ | ⟨_, c', hc', hlt', _⟩
              · unfold Lex.comment at hst; rw [hg0, hg1] at hst; cases hst
              · unfold Lex.comment at hst; rw [hg0, hg1] at hst; simp [hcl] at hst
              · unfold Lex.htmlAt at hhtmlAt
                simp only [hht, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hg0, hg1, hg2, hg3] at hhtmlAt
                cases h1 : (if first && k == 0 then (Lex.htmlClose Engine.builder cs 0).map (·, false) else none) <;>
                  (rw [h1] at hhtmlAt; simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hhtmlAt)
              · rw [hck] at hc'; injection hc' with he; subst he; rw [hlt] at hlt'; cases hlt'
            · obtain ⟨rfl, rfl⟩ := hgb hgEq
              obtain ⟨hg0, hg1, _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hd⟩
              unfold Lex.comment at hst; rw [hg0, hg1] at hst; simp at hst
            · obtain ⟨rfl, rfl⟩ := hgb hgEq
              unfold Lex.htmlAt at hhtmlAt
              simp only [hht, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Bool.and_self] at hhtmlAt
              rcases hhc : Lex.htmlClose Engine.builder cs 0 with _ | e0
              · exact absurd hd ((htmlClose_spec hok hcp hht 0).2 hhc j dtHC)
              · simp [hhc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hhtmlAt
      · rw [hhtmlAt] at hst; cases hst
  · exact hisTok

theorem stepTrivia_none_no_triviaElem (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {k : Nat}
    (hst : stepTrivia cs first cx k = none) :
    ¬ ∃ j e, TriviaElem Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first k j e := by
  rintro ⟨j, ⟨ei, ej, eg, et⟩, _, hjLen, hei, hej, hnotTok, hegoal, hder, _⟩
  dsimp only at hei hej hegoal hnotTok hder
  cases hei; cases hej
  let g0 : NT := if first && k == 0 then .InputElementHashbangOrRegExp else .InputElementDiv
  have hg0 : isLexGoal g0 = true := by dsimp only [g0]; split <;> decide
  have hgb0 : g0 = .InputElementHashbangOrRegExp → first = true ∧ k = 0 := by
    dsimp only [g0]; split
    · rename_i hif; intro _; simpa [Bool.and_eq_true, beq_iff_eq] using hif
    · intro h; cases h
  have hegEq : eg = g0 := hegoal
  subst hegEq
  have hisTok := stepTrivia_none_no_nontoken hok hcp hst hg0 hgb0 (by simpa using hjLen) hder
  rw [hisTok] at hnotTok; cases hnotTok

/-- Contiguous input element spans from `a` to `b`. -/
inductive ChainEls : Nat → Nat → List Element → Prop where
  | nil (a : Nat) : ChainEls a a []
  | cons {a m b : Nat} (e : Element) {es : List Element} :
      e.i = a → e.j = m → ChainEls m b es → ChainEls a b (e :: es)

theorem ChainEls.append {a b c : Nat} {es1 es2 : List Element}
    (h1 : ChainEls a b es1) (h2 : ChainEls b c es2) : ChainEls a c (es1 ++ es2) := by
  induction h1 with
  | nil _ => exact h2
  | cons e hi hj _ ih => exact .cons e hi hj (ih h2)

/-- Valid non-token trivia element (ready for `Scans` and `GoalsAt`). -/
def ValidTrivEl (cx : Ctx) (cs : Array Nat) (first : Bool) (e : Element) : Prop :=
  e.i < e.j ∧ e.j ≤ cs.size ∧
  e.isToken = false ∧
  e.goal = (if first && e.i == 0 then .InputElementHashbangOrRegExp else .InputElementDiv) ∧
  LexDerives cx cs e.goal [] e.i e.j e.tree ∧
  (∀ h, e.j < h → h ≤ cs.toList.length → ¬ ∃ t, LexDerives cx cs e.goal [] e.i h t) ∧
  e.tree.has .NumericLiteral e.i e.j = false

private theorem skipFrom_spec (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (first : Bool) :
    ∀ (rem : Nat) (f k : Nat) (lt0 : Bool),
      cs.size - k = rem →
      cs.size - k + 1 ≤ f →
      let (k', lt') := Lex.skipFrom Engine.builder cs first cx f k lt0
      k ≤ k' ∧ (k ≤ cs.size → k' ≤ cs.size) ∧
      stepTrivia cs first cx k' = none ∧
      ∃ lt1 els,
        lt' = (lt0 || lt1) ∧
        Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first k k' lt1 ∧
        ChainEls k k' els ∧
        (∀ e ∈ els, ValidTrivEl cx cs first e) ∧
        (els.any fun e => e.breaks cs.toList) = lt1 := by
  intro rem
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro f k lt0 hrem hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [skipFrom_succ]
    rcases hst : stepTrivia cs first cx k with _ | ⟨m, l⟩
    · dsimp only
      refine ⟨Nat.le_refl _, id, hst, false, [], (Bool.or_false lt0).symm,
        .stop (stepTrivia_none_no_triviaElem hok hcp hst), .nil k, (fun _ h => nomatch h), rfl⟩
    · dsimp only
      obtain ⟨hkm, hmSz, ⟨e0, hte0, hbr0, hhas0⟩, _⟩ := stepTrivia_some_spec hok hcp hst
      have ⟨hmk', hk'Sz, hst', lt2, els2, hltEq, htr2, hch2, hv2, hbr2⟩ :=
        ih (cs.size - m) (by omega) f' m (lt0 || l) rfl (by omega)
      have ⟨_, _, hei, hej, hnotTok, hegoal, hder, hmax⟩ := hte0
      have hv0 : ValidTrivEl cx cs first e0 :=
        ⟨by rw [hei, hej]; exact hkm,
         by rw [hej]; exact hmSz,
         Bool.eq_false_iff.mpr (by simpa using hnotTok),
         by rw [hei]; exact hegoal,
         by rw [hei, hej]; exact hder,
         by rw [hei, hej]; exact hmax,
         by rw [hei, hej]; exact hhas0⟩
      refine ⟨by omega, fun _ => hk'Sz hmSz, hst', l || lt2, e0 :: els2, ?_, ?_,
        .cons e0 hei hej hch2, ?_, ?_⟩
      · rw [hltEq, Bool.or_assoc]
      · rw [← hbr0] at htr2 ⊢; exact .step e0 hte0 htr2
      · intro e he; rcases List.mem_cons.mp he with rfl | hmem
        · exact hv0
        · exact hv2 e hmem
      · simp only [List.any_cons, hbr0, hbr2]

theorem skip_spec (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) (first : Bool) (i : Nat) :
    i ≤ (Lex.skip Engine.builder cs first cx i).1 ∧
    (i ≤ cs.size → (Lex.skip Engine.builder cs first cx i).1 ≤ cs.size) ∧
    stepTrivia cs first cx (Lex.skip Engine.builder cs first cx i).1 = none ∧
    Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first i
      (Lex.skip Engine.builder cs first cx i).1 (Lex.skip Engine.builder cs first cx i).2 ∧
    ∃ els, ChainEls i (Lex.skip Engine.builder cs first cx i).1 els ∧
      (∀ e ∈ els, ValidTrivEl cx cs first e) ∧
      (els.any fun e => e.breaks cs.toList) = (Lex.skip Engine.builder cs first cx i).2 := by
  unfold Lex.skip
  have ⟨hik, hkSz, hst, lt1, els, hltEq, htr, hch, hv, hbr⟩ :=
    skipFrom_spec (cx := cx) hok hcp first (cs.size - i) (cs.size - i + 1) i false rfl (Nat.le_refl _)
  rw [Bool.false_or] at hltEq
  subst hltEq
  exact ⟨hik, hkSz, hst, htr, els, hch, hv, hbr⟩

theorem trivia_to_skipFrom (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {i k : Nat} {lt : Bool}
    (htr : Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first i k lt) :
    ∀ (f : Nat) (lt0 : Bool), cs.size - i + 1 ≤ f →
      Lex.skipFrom Engine.builder cs first cx f i lt0 = (k, lt0 || lt) := by
  induction htr with
  | @stop i0 hno =>
    intro f lt0 hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [skipFrom_succ]
    rcases hst : stepTrivia cs first cx i0 with _ | ⟨m, l⟩
    · simp
    · obtain ⟨_, _, ⟨e0, hte0, _⟩, _⟩ := stepTrivia_some_spec hok hcp hst
      exact absurd ⟨m, e0, hte0⟩ hno
  | @step i0 m0 k0 lt1 e0 hte0 _ ih =>
    intro f lt0 hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [skipFrom_succ]
    rcases hst : stepTrivia cs first cx i0 with _ | ⟨m, l⟩
    · exact absurd ⟨m0, e0, hte0⟩ (stepTrivia_none_no_triviaElem hok hcp hst)
    · obtain ⟨him, hmSz, _, huniq⟩ := stepTrivia_some_spec hok hcp hst
      obtain ⟨rfl, hbrEq⟩ := huniq m0 e0 hte0
      dsimp only
      rw [ih f' (lt0 || l) (by omega), hbrEq, Bool.or_assoc]

theorem trivia_eq_skip (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {i k : Nat} {lt : Bool} :
    Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first i k lt ↔
      Lex.skip Engine.builder cs first cx i = (k, lt) := by
  constructor
  · intro htr
    have h := trivia_to_skipFrom hok hcp htr (cs.size - i + 1) false (Nat.le_refl _)
    simpa [Lex.skip] using h
  · intro hsk
    have ⟨_, _, _, htr, _⟩ := skip_spec (cx := cx) hok hcp first i
    rw [hsk] at htr
    exact htr

theorem trivia_unique (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {i k1 k2 : Nat} {lt1 lt2 : Bool}
    (h1 : Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first i k1 lt1)
    (h2 : Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first i k2 lt2) :
    k1 = k2 ∧ lt1 = lt2 := by
  rw [trivia_eq_skip hok hcp] at h1 h2
  exact Prod.mk.inj (h1.symm.trans h2)

/-! ### §12.9.3 `NumericLiteral` follow rule (`follow_check_iff`) -/

private theorem decimalDigit_one_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {j c : Nat} (hc : cs[j]? = some c) :
    (∃ t, LexDerives cx cs .DecimalDigit [] j (j + 1) t) ↔ (0x30 ≤ c ∧ c ≤ 0x39) := by
  have hj1Sz : j + 1 ≤ cs.size := (extract_one_eq hc).1
  have halts := alts_fixed_eq (cx := cx)
    alts_cert_tokens.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    alts_cert_tokens.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  constructor
  · rintro ⟨t, hd⟩
    obtain ⟨_, _, hpl⟩ := lexDerives_to_plain hok hj1Sz hd
    cases hpl with
    | node s hs _ _ _ hsw =>
      have hs := lex_mem_alts hok hs
      rw [halts] at hs
      unfold srcsOf writtenAlts Gen.Lexical.DecimalDigit at hs
      dsimp only [List.flatten, List.map, List.zipIdx] at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · cases hsw with | term ht _ => obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x30) (csRest := []) rfl ht; rw [hc] at hg0; injection hg0 with he; subst he; omega
      · rcases List.mem_cons.mp hs with rfl | hs
        · cases hsw with | term ht _ => obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x31) (csRest := []) rfl ht; rw [hc] at hg0; injection hg0 with he; subst he; omega
        · rcases List.mem_cons.mp hs with rfl | hs
          · cases hsw with | term ht _ => obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x32) (csRest := []) rfl ht; rw [hc] at hg0; injection hg0 with he; subst he; omega
          · rcases List.mem_cons.mp hs with rfl | hs
            · cases hsw with | term ht _ => obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x33) (csRest := []) rfl ht; rw [hc] at hg0; injection hg0 with he; subst he; omega
            · rcases List.mem_cons.mp hs with rfl | hs
              · cases hsw with | term ht _ => obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x34) (csRest := []) rfl ht; rw [hc] at hg0; injection hg0 with he; subst he; omega
              · rcases List.mem_cons.mp hs with rfl | hs
                · cases hsw with | term ht _ => obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x35) (csRest := []) rfl ht; rw [hc] at hg0; injection hg0 with he; subst he; omega
                · rcases List.mem_cons.mp hs with rfl | hs
                  · cases hsw with | term ht _ => obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x36) (csRest := []) rfl ht; rw [hc] at hg0; injection hg0 with he; subst he; omega
                  · rcases List.mem_cons.mp hs with rfl | hs
                    · cases hsw with | term ht _ => obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x37) (csRest := []) rfl ht; rw [hc] at hg0; injection hg0 with he; subst he; omega
                    · rcases List.mem_cons.mp hs with rfl | hs
                      · cases hsw with | term ht _ => obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x38) (csRest := []) rfl ht; rw [hc] at hg0; injection hg0 with he; subst he; omega
                      · rcases List.mem_cons.mp hs with rfl | hs
                        · cases hsw with | term ht _ => obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x39) (csRest := []) rfl ht; rw [hc] at hg0; injection hg0 with he; subst he; omega
                        · cases hs
  · rintro ⟨hlo, hhi⟩
    obtain ⟨_, hex1⟩ := extract_one_eq hc
    have hcases : c = 0x30 ∨ c = 0x31 ∨ c = 0x32 ∨ c = 0x33 ∨ c = 0x34 ∨
                  c = 0x35 ∨ c = 0x36 ∨ c = 0x37 ∨ c = 0x38 ∨ c = 0x39 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨_, hd⟩ := mkLexPlainSimple hok (mem_alts_of_get? halts 0 rfl) rfl (.term (termEnd_text_mk "0" false j (by decide) hj1Sz hex1) .nil)
      exact ⟨_, (lexPlain_to_derives hok (by omega) hd).2.2⟩
    · obtain ⟨_, hd⟩ := mkLexPlainSimple hok (mem_alts_of_get? halts 1 rfl) rfl (.term (termEnd_text_mk "1" false j (by decide) hj1Sz hex1) .nil)
      exact ⟨_, (lexPlain_to_derives hok (by omega) hd).2.2⟩
    · obtain ⟨_, hd⟩ := mkLexPlainSimple hok (mem_alts_of_get? halts 2 rfl) rfl (.term (termEnd_text_mk "2" false j (by decide) hj1Sz hex1) .nil)
      exact ⟨_, (lexPlain_to_derives hok (by omega) hd).2.2⟩
    · obtain ⟨_, hd⟩ := mkLexPlainSimple hok (mem_alts_of_get? halts 3 rfl) rfl (.term (termEnd_text_mk "3" false j (by decide) hj1Sz hex1) .nil)
      exact ⟨_, (lexPlain_to_derives hok (by omega) hd).2.2⟩
    · obtain ⟨_, hd⟩ := mkLexPlainSimple hok (mem_alts_of_get? halts 4 rfl) rfl (.term (termEnd_text_mk "4" false j (by decide) hj1Sz hex1) .nil)
      exact ⟨_, (lexPlain_to_derives hok (by omega) hd).2.2⟩
    · obtain ⟨_, hd⟩ := mkLexPlainSimple hok (mem_alts_of_get? halts 5 rfl) rfl (.term (termEnd_text_mk "5" false j (by decide) hj1Sz hex1) .nil)
      exact ⟨_, (lexPlain_to_derives hok (by omega) hd).2.2⟩
    · obtain ⟨_, hd⟩ := mkLexPlainSimple hok (mem_alts_of_get? halts 6 rfl) rfl (.term (termEnd_text_mk "6" false j (by decide) hj1Sz hex1) .nil)
      exact ⟨_, (lexPlain_to_derives hok (by omega) hd).2.2⟩
    · obtain ⟨_, hd⟩ := mkLexPlainSimple hok (mem_alts_of_get? halts 7 rfl) rfl (.term (termEnd_text_mk "7" false j (by decide) hj1Sz hex1) .nil)
      exact ⟨_, (lexPlain_to_derives hok (by omega) hd).2.2⟩
    · obtain ⟨_, hd⟩ := mkLexPlainSimple hok (mem_alts_of_get? halts 8 rfl) rfl (.term (termEnd_text_mk "8" false j (by decide) hj1Sz hex1) .nil)
      exact ⟨_, (lexPlain_to_derives hok (by omega) hd).2.2⟩
    · obtain ⟨_, hd⟩ := mkLexPlainSimple hok (mem_alts_of_get? halts 9 rfl) rfl (.term (termEnd_text_mk "9" false j (by decide) hj1Sz hex1) .nil)
      exact ⟨_, (lexPlain_to_derives hok (by omega) hd).2.2⟩

private theorem identifierStart_one_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {j c : Nat} (hc : cs[j]? = some c) :
    Code.dec Engine.builder cs .lexical cx 16 .IdentifierStart [] j (j + 1) =
      (Engine.builder.idStart c || c == 0x24 || c == 0x5F) ∧
    ((∃ t, LexDerives cx cs .IdentifierStart [] j (j + 1) t) ↔
      (Engine.builder.idStart c = true ∨ c = 0x24 ∨ c = 0x5F)) := by
  obtain ⟨hj1Sz, hex1⟩ := extract_one_eq hc
  have haltsIS := alts_fixed_eq (cx := cx) alts_cert_tokens.2.2.2.2.2.2.1 alts_cert_tokens.2.2.2.2.2.2.2.1
  have haltsISC := alts_fixed_eq (cx := cx) alts_cert_tokens.2.2.2.2.2.2.2.2.1 alts_cert_tokens.2.2.2.2.2.2.2.2.2.1
  have haltsUID := alts_fixed_eq (cx := cx) alts_cert_tokens.2.2.2.2.2.2.2.2.2.2.1 alts_cert_tokens.2.2.2.2.2.2.2.2.2.2.2.1
  have haltsUES := alts_fixed_eq (cx := cx) alts_cert_tokens.2.2.2.2.2.2.2.2.2.2.2.2.1 alts_cert_tokens.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdecUES0 : Code.dec Engine.builder cs .lexical cx 15 .UnicodeEscapeSequence [] (j + 1) (j + 1) = false := by
    unfold Code.dec
    rw [altsOf_eq hok, haltsUES]
    simp only [srcsOf, writtenAlts, Gen.Lexical.UnicodeEscapeSequence, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, List.all_nil, Bool.true_and,
      Code.decSeq, Bool.false_and, Bool.false_or]
    cases hte1 : Code.termEnd Engine.builder cs (.text "u" false) (j + 1) with
    | none =>
      cases hte2 : Code.termEnd Engine.builder cs (.text "u{" false) (j + 1) with
      | none => rfl
      | some j1 =>
        have hlt := (codeTerm_bound Engine.builder cs (.text "u{" false) (j + 1) j1 hte2).1
        simp [decide_eq_false (by omega : ¬ j1 ≤ j + 1)]
    | some j1 =>
      have hlt := (codeTerm_bound Engine.builder cs (.text "u" false) (j + 1) j1 hte1).1
      cases hte2 : Code.termEnd Engine.builder cs (.text "u{" false) (j + 1) with
      | none => simp [decide_eq_false (by omega : ¬ j1 ≤ j + 1)]
      | some j2 =>
        have hlt2 := (codeTerm_bound Engine.builder cs (.text "u{" false) (j + 1) j2 hte2).1
        simp [decide_eq_false (by omega : ¬ j1 ≤ j + 1), decide_eq_false (by omega : ¬ j2 ≤ j + 1)]
  have hdecUID : ∀ d, d < 2 →
      (Code.dec Engine.builder cs .lexical cx 14 .UnicodeIDStart [] j (j + d) && (j + d == j + 1)) =
      (decide (d = 1) && Engine.builder.idStart c) := by
    intro d hd
    have hdOr : d = 0 ∨ d = 1 := by omega
    rcases hdOr with rfl | rfl
    · simp
    · unfold Code.dec
      rw [altsOf_eq hok, haltsUID]
      simp [srcsOf, writtenAlts, Gen.Lexical.UnicodeIDStart, Code.decSeq, hc, Code.phraseOk]
  have hdecISC : ∀ d, d < 2 →
      (Code.dec Engine.builder cs .lexical cx 15 .IdentifierStartChar [] j (j + d) && (j + d == j + 1)) =
      (decide (d = 1) && (Engine.builder.idStart c || c == 0x24 || c == 0x5F)) := by
    intro d hd
    have hdOr : d = 0 ∨ d = 1 := by omega
    rcases hdOr with rfl | rfl
    · simp
    · unfold Code.dec
      rw [altsOf_eq hok, haltsISC]
      simp only [srcsOf, writtenAlts, Gen.Lexical.IdentifierStartChar, List.zipIdx_cons, List.zipIdx_nil,
        List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, List.all_nil, Bool.true_and,
        Code.decSeq, applyArgs, List.filterMap_nil, Bool.false_and, Bool.false_or,
        show j + 1 + 1 - j = 2 from by omega, List.range_succ, List.range_zero, List.nil_append, List.cons_append]
      rw [hdecUID 0 (by omega), hdecUID 1 (by omega)]
      by_cases h24 : c = 0x24
      · subst h24
        rw [termEnd_text_mk "$" false j (by decide) hj1Sz hex1]
        cases hteU : Code.termEnd Engine.builder cs (.text "_" false) j with
        | none => simp
        | some j1 =>
          obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x5F) (csRest := []) rfl hteU
          rw [hc] at hg0; cases hg0
      · cases hteD : Code.termEnd Engine.builder cs (.text "$" false) j with
        | some j1 =>
          obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x24) (csRest := []) rfl hteD
          exact absurd (Option.some.inj (hc.symm.trans hg0)) h24
        | none =>
          by_cases h5f : c = 0x5F
          · subst h5f
            rw [termEnd_text_mk "_" false j (by decide) hj1Sz hex1]
            simp
          · cases hteU : Code.termEnd Engine.builder cs (.text "_" false) j with
            | none => simp [beq_eq_false_iff_ne.mpr h24, beq_eq_false_iff_ne.mpr h5f]
            | some j1 =>
              obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x5F) (csRest := []) rfl hteU
              exact absurd (Option.some.inj (hc.symm.trans hg0)) h5f
  have hdecIS : Code.dec Engine.builder cs .lexical cx 16 .IdentifierStart [] j (j + 1) =
      (Engine.builder.idStart c || c == 0x24 || c == 0x5F) := by
    unfold Code.dec
    rw [altsOf_eq hok, haltsIS]
    simp only [srcsOf, writtenAlts, Gen.Lexical.IdentifierStart, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, List.all_nil, Bool.true_and,
      Code.decSeq, applyArgs, List.filterMap_nil, Bool.false_and, Bool.false_or,
      show j + 1 + 1 - j = 2 from by omega, List.range_succ, List.range_zero, List.nil_append, List.cons_append]
    rw [hdecISC 0 (by omega), hdecISC 1 (by omega)]
    cases hte : Code.termEnd Engine.builder cs (.text "\\" false) j with
    | none => simp
    | some j1 =>
      obtain ⟨hmid, _, _⟩ := termEnd_text_cons (c0 := 0x5C) (csRest := []) rfl hte
      simp at hmid; subst hmid
      simp [hdecUES0]
  refine ⟨hdecIS, ?_⟩
  constructor
  · rintro ⟨t, hd⟩
    obtain ⟨_, _, hpl⟩ := lexDerives_to_plain hok hj1Sz hd
    cases hpl with
    | node s hs _ _ _ hsw =>
      have hs := lex_mem_alts hok hs
      rw [haltsIS] at hs
      simp only [srcsOf, writtenAlts, Gen.Lexical.IdentifierStart, List.zipIdx_cons, List.zipIdx_nil,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · cases hsw with
        | leaf _ hl _ _ _ => exact nomatch hl
        | nt _ hdISC _ _ hnil =>
          cases hnil
          cases hdISC with
          | node sc hsc _ _ _ hswC =>
            have hsc := lex_mem_alts hok hsc
            rw [haltsISC] at hsc
            simp only [srcsOf, writtenAlts, Gen.Lexical.IdentifierStartChar, List.zipIdx_cons, List.zipIdx_nil,
              List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsc
            rcases hsc with rfl | rfl | rfl
            · cases hswC with
              | leaf _ hl _ _ _ => exact nomatch hl
              | nt _ hdU _ _ hnil2 =>
                cases hnil2
                cases hdU with
                | node su hsu _ _ _ hswU =>
                  have hsu := lex_mem_alts hok hsu
                  rw [haltsUID] at hsu
                  simp [srcsOf, writtenAlts, Gen.Lexical.UnicodeIDStart] at hsu; subst hsu
                  cases hswU with
                  | phrase hph _ =>
                    obtain ⟨c', hc', hpok, _⟩ := hph
                    rw [hc] at hc'; injection hc' with he; subst he
                    exact Or.inl hpok
            · cases hswC with | term ht _ =>
                obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x24) (csRest := []) rfl ht
                exact Or.inr (Or.inl (Option.some.inj (hc.symm.trans hg0)))
            · cases hswC with | term ht _ =>
                obtain ⟨_, hg0, _⟩ := termEnd_text_cons (c0 := 0x5F) (csRest := []) rfl ht
                exact Or.inr (Or.inr (Option.some.inj (hc.symm.trans hg0)))
      · cases hsw with
        | term ht hr =>
          obtain ⟨hmid, _, _⟩ := termEnd_text_cons (c0 := 0x5C) (csRest := []) rfl ht
          simp at hmid; subst hmid
          cases hr with
          | leaf _ hl _ _ _ => exact nomatch hl
          | nt _ hdUES _ _ hnil =>
            cases hnil
            cases hdUES with
            | node su hsu _ _ _ hswU =>
              have hsu := lex_mem_alts hok hsu
              rw [haltsUES] at hsu
              simp only [srcsOf, writtenAlts, Gen.Lexical.UnicodeEscapeSequence, List.zipIdx_cons, List.zipIdx_nil,
                List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsu
              rcases hsu with rfl | rfl <;> (
                cases hswU with | term htu hrU =>
                  obtain ⟨hmidU, _, _⟩ := termEnd_text_cons rfl htu
                  have ⟨hleU, _⟩ := lexSeqWith_le hok (codeTerm_bound Engine.builder cs _ _ _ htu).2 hrU
                  simp at hmidU; omega)
  · intro hcond
    have hsIS0 : ⟨.lexical, Gen.Lexical.IdentifierStart, 0, ⟨[], [.sym (.nt .IdentifierStartChar []) false], none⟩⟩ ∈
        Ecma.Spec.gl.alts cx .lexical .IdentifierStart := mem_alts_of_get? haltsIS 0 rfl
    have hneISC : (altsOf cx .lexical .IdentifierStartChar).isEmpty = false := altsOf_nonempty_of_srcs1 hok haltsISC rfl
    have hmkISC : ∃ dtISC, (lexSpec cs cx).PlainDerives .IdentifierStartChar [] j (j + 1) dtISC := by
      rcases hcond with hid | rfl | rfl
      · have hsU : ⟨.lexical, Gen.Lexical.UnicodeIDStart, 0, ⟨[], [.phrase .idStart], none⟩⟩ ∈
            Ecma.Spec.gl.alts cx .lexical .UnicodeIDStart := mem_alts_of_get? haltsUID 0 rfl
        have hsISC0 : ⟨.lexical, Gen.Lexical.IdentifierStartChar, 0, ⟨[], [.sym (.nt .UnicodeIDStart []) false], none⟩⟩ ∈
            Ecma.Spec.gl.alts cx .lexical .IdentifierStartChar := mem_alts_of_get? haltsISC 0 rfl
        obtain ⟨_, hdU⟩ := mkLexPlainSimple hok hsU rfl (.phrase ⟨c, hc, hid, rfl⟩ .nil)
        obtain ⟨_, hdC⟩ := mkLexPlainSimple hok hsISC0 rfl (.nt (altsOf_nonempty_of_mem hok hsU) hdU rfl trivial .nil)
        exact ⟨_, hdC⟩
      · have hsISC1 : ⟨.lexical, Gen.Lexical.IdentifierStartChar, 1, ⟨[], [.sym (.t (.text "$" false)) false], none⟩⟩ ∈
            Ecma.Spec.gl.alts cx .lexical .IdentifierStartChar := mem_alts_of_get? haltsISC 1 rfl
        obtain ⟨_, hdC⟩ := mkLexPlainSimple hok hsISC1 rfl (.term (termEnd_text_mk "$" false j (by decide) hj1Sz hex1) .nil)
        exact ⟨_, hdC⟩
      · have hsISC2 : ⟨.lexical, Gen.Lexical.IdentifierStartChar, 2, ⟨[], [.sym (.t (.text "_" false)) false], none⟩⟩ ∈
            Ecma.Spec.gl.alts cx .lexical .IdentifierStartChar := mem_alts_of_get? haltsISC 2 rfl
        obtain ⟨_, hdC⟩ := mkLexPlainSimple hok hsISC2 rfl (.term (termEnd_text_mk "_" false j (by decide) hj1Sz hex1) .nil)
        exact ⟨_, hdC⟩
    obtain ⟨dtISC, hdISC⟩ := hmkISC
    obtain ⟨_, hdIS⟩ := mkLexPlainSimple hok hsIS0 rfl (.nt hneISC hdISC rfl trivial .nil)
    exact ⟨_, (lexPlain_to_derives hok (by omega) hdIS).2.2⟩

theorem follow_check_iff (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {j c : Nat} (hc : cs[j]? = some c) :
    ((decide (0x30 ≤ c) && decide (c ≤ 0x39)) ||
      Code.dec Engine.builder cs .lexical cx 16 .IdentifierStart [] j (j + 1)) = true ↔
      ∃ n ∈ [NT.IdentifierStart, NT.DecimalDigit], ∃ t, LexDerives cx cs n [] j (j + 1) t := by
  obtain ⟨hdecIS, hisIff⟩ := identifierStart_one_iff hok hc
  have hddIff := decimalDigit_one_iff hok (cx := cx) hc
  rw [hdecIS]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (hd | ((hid | h24) | h5f))
    · exact ⟨.DecimalDigit, Or.inr rfl, hddIff.mpr hd⟩
    · exact ⟨.IdentifierStart, Or.inl rfl, hisIff.mpr (Or.inl hid)⟩
    · exact ⟨.IdentifierStart, Or.inl rfl, hisIff.mpr (Or.inr (Or.inl h24))⟩
    · exact ⟨.IdentifierStart, Or.inl rfl, hisIff.mpr (Or.inr (Or.inr h5f))⟩
  · rintro ⟨n, rfl | rfl, ht⟩
    · rcases hisIff.mp ht with hid | h24 | h5f
      · exact Or.inr (Or.inl (Or.inl hid))
      · exact Or.inr (Or.inl (Or.inr h24))
      · exact Or.inr (Or.inr h5f)
    · exact Or.inl (hddIff.mp ht)

/-! ### `lexFound`, `furthest`, and `lexAtPure_ok_spec` -/

private theorem furthest_spec (found : List (NT × Nat)) (k : Nat)
    (_hge : ∀ p ∈ found, k ≤ p.2) :
    k ≤ Lex.furthest found k ∧
    (∀ p ∈ found, p.2 ≤ Lex.furthest found k) ∧
    (Lex.furthest found k = k ∨ ∃ p ∈ found, p.2 = Lex.furthest found k) := by
  unfold Lex.furthest
  have hfold : ∀ (xs : List (NT × Nat)) (acc : Nat),
      k ≤ acc →
      (acc = k ∨ ∃ p ∈ found, p.2 = acc) →
      (∀ p ∈ xs, p ∈ found) →
      let res := xs.foldl (fun m e => max m e.2) acc
      acc ≤ res ∧ (∀ p ∈ xs, p.2 ≤ res) ∧ (res = k ∨ ∃ p ∈ found, p.2 = res) := by
    intro xs
    induction xs with
    | nil => intro acc _ hwit _; exact ⟨Nat.le_refl _, (fun _ h => nomatch h), hwit⟩
    | cons hd tl ih =>
      intro acc hkacc hwit hsub
      simp only [List.foldl_cons]
      have hhdF : hd ∈ found := hsub hd (List.mem_cons_self ..)
      have hwit' : max acc hd.2 = k ∨ ∃ p ∈ found, p.2 = max acc hd.2 := by
        by_cases hle : hd.2 ≤ acc
        · rw [Nat.max_eq_left hle]; exact hwit
        · rw [Nat.max_eq_right (by omega)]; exact Or.inr ⟨hd, hhdF, rfl⟩
      have ⟨h1, h2, h3⟩ := ih (max acc hd.2) (Nat.le_trans hkacc (Nat.le_max_left _ _)) hwit'
        (fun p hp => hsub p (List.mem_cons_of_mem _ hp))
      refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun p hp => ?_, h3⟩
      rcases List.mem_cons.mp hp with rfl | htl
      · exact Nat.le_trans (Nat.le_max_right _ _) h1
      · exact h2 p htl
  have ⟨h1, h2, h3⟩ := hfold found k (Nat.le_refl _) (Or.inl rfl) (fun _ h => h)
  exact ⟨h1, h2, h3⟩

private theorem lexFound_spec (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (g : NT) (k : Nat) (hk : k < cs.size) (st : St Unit) (found : List (NT × Nat)) (st' : St Unit)
    (hmi : (lexSpec cs cx).MemoInv none st)
    (hna : ∀ x, st.active.contains x = false)
    (hrun : (Lex.lexFound Engine.builder cs cx g k).run st = .ok (found, st')) :
    (lexSpec cs cx).MemoInv none st' ∧
    (∀ x, st'.active.contains x = false) ∧
    st'.fwd = st.fwd ∧
    found.map Prod.fst = Lex.classes g ∧
    ∀ c m, (c, m) ∈ found →
      k ≤ m ∧ m ≤ cs.size ∧
      (m = k ∨ (k < m ∧ ∃ dt, (lexSpec cs cx).PlainDerives c [] k m dt)) ∧
      (∀ x dt, (lexSpec cs cx).PlainDerives c [] k x dt → x ≤ m) := by
  unfold Lex.lexFound at hrun
  have hmapM : ∀ (clsList : List NT) (s0 : St Unit) (out : List (NT × Nat)) (s1 : St Unit),
      (lexSpec cs cx).MemoInv none s0 →
      (∀ x, s0.active.contains x = false) →
      (clsList.mapM (fun c => do
        return (c, (← finalEnds (Code.alpha Engine.builder cs .lexical cx) cs.size (Code.depth cs.size) c [] k).maxFrom k))).run s0 = .ok (out, s1) →
      (lexSpec cs cx).MemoInv none s1 ∧
      (∀ x, s1.active.contains x = false) ∧
      s1.fwd = s0.fwd ∧
      out.map Prod.fst = clsList ∧
      ∀ c m, (c, m) ∈ out →
        k ≤ m ∧ m ≤ cs.size ∧
        (m = k ∨ (k < m ∧ ∃ dt, (lexSpec cs cx).PlainDerives c [] k m dt)) ∧
        (∀ x dt, (lexSpec cs cx).PlainDerives c [] k x dt → x ≤ m) := by
    intro clsList
    induction clsList with
    | nil =>
      intro s0 out s1 hmi0 hna0 hr
      simp only [List.mapM_nil] at hr
      obtain ⟨rfl, rfl⟩ := sm_pure_ok hr
      exact ⟨hmi0, hna0, rfl, rfl, fun _ _ h => nomatch h⟩
    | cons c0 rest ih =>
      intro s0 out s1 hmi0 hna0 hr
      simp only [List.mapM_cons] at hr
      obtain ⟨hdPair, smid, hhd, hrTail⟩ := sm_bind_ok hr
      obtain ⟨tlOut, s2, htl, hpure⟩ := sm_bind_ok hrTail
      obtain ⟨rfl, rfl⟩ := sm_pure_ok hpure
      obtain ⟨es, smid0, hfe, hpHd⟩ := sm_bind_ok hhd
      obtain ⟨rfl, rfl⟩ := sm_pure_ok hpHd
      have ⟨hmiMid, hnaMid, hfwMid, hesIff⟩ :=
        (lexSpec cs cx).finalEnds_spec hok (Or.inr lexical_mem_codeGrammars) (Code.depth cs.size)
          c0 [] k s0 es smid hmi0 hna0 hfe
      have ⟨hmi1, hna1, hfw1, hmapTl, hallTl⟩ := ih smid tlOut s1 hmiMid hnaMid htl
      refine ⟨hmi1, hna1, hfw1.trans hfwMid, by simp [hmapTl], fun c m hcm => ?_⟩
      rcases List.mem_cons.mp hcm with hEq | htlMem
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
        have hkLeM : k ≤ es.maxFrom k := Ends.maxFrom_ge es k
        have hub : ∀ x dt, (lexSpec cs cx).PlainDerives c [] k x dt → x ≤ es.maxFrom k := by
          intro x dt hpl
          have hmd := (lexMode_iff_plain hok (Nat.le_of_lt hk)).mpr hpl
          exact Ends.maxFrom_ub es k x ((hesIff x).mpr ⟨dt, hmd⟩)
        rcases Ends.maxFrom_eq_or_mem es k with heqK | ⟨hltM, hmemM⟩
        · exact ⟨hkLeM, by omega, Or.inl heqK, hub⟩
        · obtain ⟨dtM, hmdM⟩ := (hesIff (es.maxFrom k)).mp hmemM
          have hplM := (lexMode_iff_plain hok (Nat.le_of_lt hk)).mp hmdM
          have ⟨_, hmSz, _⟩ := lexPlain_to_derives hok (Nat.le_of_lt hk) hplM
          exact ⟨hkLeM, hmSz, Or.inr ⟨hltM, dtM, hplM⟩, hub⟩
      · exact hallTl c m htlMem
  exact hmapM (Lex.classes g) st found st' hmi hna hrun

/-- Specification of `Lex.lexAtPure`'s result `res` from position `i` under lexical `goal`. -/
def LexAtPureSpec (cx : Ctx) (cs : Array Nat) (first : Bool) (goal : NT) (i : Nat) (res : Lex.Lexed) : Prop :=
  let (k, lt) := Lex.skip Engine.builder cs first cx i
  Trivia Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first i k lt ∧
  match res with
  | .eof lt' =>
    lt' = lt ∧ cs.size ≤ k ∧
    (∀ a b lt0 tr, ¬ ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal i a b lt0 tr)
  | .bad pos =>
    pos = k ∧ k < cs.size ∧
    (∀ a b lt0 tr, ¬ ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal i a b lt0 tr)
  | .follow pos =>
    k < pos ∧ pos ≤ cs.size ∧ k < cs.size ∧
    (∀ a b lt0 tr, ¬ ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal i a b lt0 tr)
  | .tok tok =>
    tok.i = k ∧ tok.lt = lt ∧ i ≤ k ∧ k < tok.j ∧ tok.j ≤ cs.size ∧
    (∃ tr, ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal i k tok.j lt tr ∧
      tr.has .NumericLiteral k tok.j = (tok.cls == .NumericLiteral)) ∧
    (∀ a b lt0 tr, ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal i a b lt0 tr →
      a = k ∧ b = tok.j ∧ lt0 = lt)

/-- Full soundness and completeness characterization of `Lex.lexAtPure` when it returns `.ok res`. -/
theorem lexAtPure_ok_spec (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {goal : NT} (hgoal : isSynLexGoal goal = true)
    {i : Nat} {res : Lex.Lexed}
    (hlex : Lex.lexAtPure Engine.builder cs first cx goal i = .ok res) :
    LexAtPureSpec cx cs first goal i res := by
  unfold LexAtPureSpec
  have ⟨hik, hkSzImp, hstNone, htrSkip, _⟩ := skip_spec (cx := cx) hok hcp first i
  have hlex' := hlex
  unfold Lex.lexAtPure at hlex'
  rw [StateT.run'_eq] at hlex'
  rcases except_eq_err_or_ok ((Lex.lexAt (T := Unit) Engine.builder cs first cx goal i).run
      { steps := Code.budget cs.size }) with ⟨err, Hrun⟩ | ⟨⟨res0, stEnd⟩, Hrun⟩
  · rw [Hrun] at hlex'; cases hlex'
  · rw [Hrun] at hlex'; injection hlex' with hresEq; subst hresEq
    unfold Lex.lexAt at Hrun
    let sk := Lex.skip Engine.builder cs first cx i
    have hskEq : Lex.skip Engine.builder cs first cx i = (sk.1, sk.2) := rfl
    rw [hskEq] at htrSkip hstNone hik Hrun ⊢
    dsimp only at Hrun ⊢
    refine ⟨htrSkip, ?_⟩
    by_cases hkGe : sk.1 ≥ cs.size
    · simp only [hkGe, ↓reduceIte] at Hrun
      obtain ⟨hEq, _⟩ := sm_pure_ok Hrun
      cases hEq.symm
      refine ⟨rfl, hkGe, fun a b lt0 tr hscan => ?_⟩
      obtain ⟨htrA, hab, hbLen, _⟩ := hscan
      obtain ⟨rfl, _⟩ := trivia_unique hok hcp htrSkip htrA
      have hbSz : b ≤ cs.size := by simpa using hbLen
      omega
    · have hkLt : sk.1 < cs.size := by omega
      have hkLe : sk.1 ≤ cs.size := Nat.le_of_lt hkLt
      simp only [hkGe, ↓reduceIte] at Hrun
      let g := if first && sk.1 == 0 then NT.InputElementHashbangOrRegExp else goal
      have hgLex : isLexGoal g = true := by
        dsimp only [g]; split
        · decide
        · exact isLexGoal_of_isSynLexGoal hgoal
      have hgb : g = .InputElementHashbangOrRegExp → first = true ∧ sk.1 = 0 := by
        dsimp only [g]; split
        · rename_i hif; intro _; simpa [Bool.and_eq_true, beq_iff_eq] using hif
        · intro hgEq; rw [hgEq] at hgoal; cases hgoal
      obtain ⟨found, st1, hlfRun, hr1⟩ := sm_bind_ok Hrun
      have hmi0 : (lexSpec cs cx).MemoInv none { steps := Code.budget cs.size } :=
        AlphaSpec.MemoInv.fresh (lexSpec cs cx) trivial rfl rfl rfl rfl none
      have hna0 : ∀ x, ({ steps := Code.budget cs.size } : St Unit).active.contains x = false :=
        fun x => hs_empty x
      have ⟨hmi1, hna1, hfw1, hmapFst, hallFound⟩ := lexFound_spec hok g sk.1 hkLt _ found st1 hmi0 hna0 hlfRun
      let j := Lex.furthest found sk.1
      have ⟨hkLeJ, hubFound, hjOr⟩ := furthest_spec found sk.1 (fun ⟨c, m⟩ hcm => (hallFound c m hcm).1)
      rw [show Lex.furthest found sk.1 = j from rfl] at hr1
      -- Helper: any token class `c ∈ Lex.classes g` deriving `(sk.1, x)` has `x ≤ j`:
      have hclsUbJ : ∀ c ∈ Lex.classes g, ∀ x dt, (lexSpec cs cx).PlainDerives c [] sk.1 x dt → x ≤ j := by
        intro c hcMem x dt hpl
        have hcInMap : c ∈ found.map Prod.fst := hmapFst ▸ hcMem
        obtain ⟨⟨c', m⟩, hcm, hcEq⟩ := List.mem_map.mp hcInMap
        dsimp only at hcEq; subst c'
        exact Nat.le_trans ((hallFound c m hcm).2.2.2 x dt hpl) (hubFound (c, m) hcm)
      by_cases hjk : (j == sk.1) = true
      · simp only [hjk, ↓reduceIte] at hr1
        obtain ⟨hEq, _⟩ := sm_pure_ok hr1
        cases hEq.symm
        have hjEqK : j = sk.1 := beq_iff_eq.mp hjk
        refine ⟨rfl, hkLt, fun a b lt0 tr hscan => ?_⟩
        obtain ⟨htrA, hab, hbLen, _, hderG, _⟩ := hscan
        obtain ⟨rfl, _⟩ := trivia_unique hok hcp htrSkip htrA
        have hbSz : b ≤ cs.size := by simpa using hbLen
        have hisTok := stepTrivia_none_no_nontoken hok hcp hstNone hgLex hgb hbSz hderG
        rcases unpackInputElement hok hgLex hbSz hderG with ⟨hnot, _⟩ | ⟨_, cls, hcls, dt, hpl, _⟩
        · rw [hisTok] at hnot; cases hnot
        · have hbLeJ := hclsUbJ cls hcls b dt hpl
          omega
      · simp only [hjk, Bool.false_eq_true, ↓reduceIte] at hr1
        have hkLtJ : sk.1 < j := by have := beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hjk); omega
        obtain ⟨hnotGtSz, hr2⟩ := sm_ite_throw_jp hr1
        have hjSz : j ≤ cs.size := by omega
        -- Since `sk.1 < j`, `hjOr` gives `p ∈ found` with `p.2 = j`, so `found.find?` MUST succeed,
        -- though handling both `none` and `some` directly is easy:
        cases hfind : found.find? (·.2 == j) with
        | none =>
          obtain ⟨⟨cMax, mMax⟩, hmMem, hmEqJ⟩ := hjOr.resolve_left (by omega)
          have hne := List.find?_eq_none.mp hfind (cMax, mMax) hmMem
          dsimp only at hmEqJ hne
          exact absurd (beq_iff_eq.mpr hmEqJ) hne
        | some pair =>
          rcases pair with ⟨cls, mCls⟩
          rw [hfind] at hr2; dsimp only at hr2
          have hpairMem : (cls, mCls) ∈ found := List.mem_of_find?_eq_some hfind
          have hmB := List.find?_some hfind
          dsimp only at hmB
          have hmClsEqJ : mCls = j := beq_iff_eq.mp hmB
          subst hmClsEqJ
          have hclsMem : cls ∈ Lex.classes g := hmapFst ▸ List.mem_map_of_mem (f := Prod.fst) hpairMem
          obtain ⟨_, _, hclsOr, _⟩ := hallFound cls j hpairMem
          obtain ⟨_, dtCls0, hplCls0⟩ := hclsOr.resolve_left (by omega)
          obtain ⟨hnotTwo, hr3⟩ := sm_ite_throw_jp hr2
          -- Unique class reaching `j`:
          have hclsUniqAtJ : ∀ cls' ∈ Lex.classes g, ∀ dt', (lexSpec cs cx).PlainDerives cls' [] sk.1 j dt' → cls' = cls := by
            intro cls' hcls' dt' hpl'
            by_cases heqC : cls' = cls
            · exact heqC
            · exfalso
              have hcInMap : cls' ∈ found.map Prod.fst := hmapFst ▸ hcls'
              obtain ⟨⟨c2, m2⟩, hm2Mem, hc2Eq⟩ := List.mem_map.mp hcInMap
              dsimp only at hc2Eq; subst c2
              have hjLeM2 := (hallFound cls' m2 hm2Mem).2.2.2 j dt' hpl'
              have hm2LeJ := hubFound (cls', m2) hm2Mem
              have hm2Eq : m2 = j := by omega
              subst hm2Eq
              have hmem1 : (cls, j) ∈ found.filter (·.2 == j) := List.mem_filter.mpr ⟨hpairMem, beq_self_eq_true j⟩
              have hmem2 : (cls', j) ∈ found.filter (·.2 == j) := List.mem_filter.mpr ⟨hm2Mem, beq_self_eq_true j⟩
              have hge2 := length_ge_two_of_ne_mem hmem1 hmem2 (fun h => heqC (Prod.mk.inj h).1.symm)
              omega
          obtain ⟨nd, st2, hbld, hr4⟩ := sm_bind_ok hr3
          obtain ⟨_, hr5⟩ := sm_unless_throw_jp hr4
          -- Check the `NumericLiteral` follow branch:
          by_cases hclsNum : (cls == .NumericLiteral) = true
          · simp only [hclsNum, ↓reduceIte] at hr5
            have hclsEqNum : cls = .NumericLiteral := beq_iff_eq.mp hclsNum
            rcases hcj : cs[j]? with _ | cj
            · rw [hcj] at hr5; dsimp only at hr5
              obtain ⟨hEq, _⟩ := sm_pure_ok hr5
              cases hEq.symm
              dsimp only
              obtain ⟨tree0, hder0, hisTok0, hhas0⟩ := packToken hok hgLex hclsMem hkLe hplCls0
              have hmax0 : ∀ h, j < h → h ≤ cs.toList.length → ¬ ∃ t, LexDerives cx cs g [] sk.1 h t := by
                intro h hjh hhLen ⟨t, hdt⟩
                have hhSz : h ≤ cs.size := by simpa using hhLen
                have hisTokH := stepTrivia_none_no_nontoken hok hcp hstNone hgLex hgb hhSz hdt
                rcases unpackInputElement hok hgLex hhSz hdt with ⟨hnot, _⟩ | ⟨_, c', hc', dt', hpl', _⟩
                · rw [hisTokH] at hnot; cases hnot
                · have := hclsUbJ c' hc' h dt' hpl'; omega
              have hjGeLen : cs.toList.length ≤ j := by
                rw [Array.length_toList]; exact Array.getElem?_eq_none_iff.mp hcj
              have hscan0 : ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal i sk.1 j sk.2 tree0 :=
                ⟨htrSkip, hkLtJ, by simpa using hjSz, hisTok0, hder0, hmax0, fun _ hjLt => absurd hjLt (by omega)⟩
              refine ⟨rfl, rfl, hik, hkLtJ, hjSz, ⟨tree0, hscan0, hhas0⟩, fun a b lt0 tr hscan => ?_⟩
              obtain ⟨htrA, _, hbLen, _, hderB, hmaxB, _⟩ := hscan
              obtain ⟨rfl, rfl⟩ := trivia_unique hok hcp htrSkip htrA
              have hbSz : b ≤ cs.size := by simpa using hbLen
              have hisTokB := stepTrivia_none_no_nontoken hok hcp hstNone hgLex hgb hbSz hderB
              rcases unpackInputElement hok hgLex hbSz hderB with ⟨hnot, _⟩ | ⟨_, c', hc', dt', hpl', _⟩
              · rw [hisTokB] at hnot; cases hnot
              · have hbLeJ := hclsUbJ c' hc' b dt' hpl'
                have hjLeB : j ≤ b := Classical.byContradiction fun hgt =>
                  hmaxB j (by omega) (by simpa using hjSz) ⟨tree0, hder0⟩
                exact ⟨rfl, by omega, rfl⟩
            · rw [hcj] at hr5; dsimp only at hr5
              by_cases hfol : ((decide (0x30 ≤ cj) && decide (cj ≤ 0x39)) ||
                  Code.dec Engine.builder cs .lexical cx 16 .IdentifierStart [] j (j + 1)) = true
              · simp only [hfol, ↓reduceIte] at hr5
                obtain ⟨hEq, _⟩ := sm_pure_ok hr5
                cases hEq.symm
                refine ⟨hkLtJ, hjSz, hkLt, fun a b lt0 tr hscan => ?_⟩
                obtain ⟨htrA, _, hbLen, _, hderB, hmaxB, hnoFolB⟩ := hscan
                obtain ⟨rfl, rfl⟩ := trivia_unique hok hcp htrSkip htrA
                have hbSz : b ≤ cs.size := by simpa using hbLen
                obtain ⟨tree0, hder0, _, _⟩ := packToken hok hgLex hclsMem hkLe hplCls0
                have hjLeB : j ≤ b := Classical.byContradiction fun hgt =>
                  hmaxB j (by omega) (by simpa using hjSz) ⟨tree0, hder0⟩
                have hisTokB := stepTrivia_none_no_nontoken hok hcp hstNone hgLex hgb hbSz hderB
                rcases unpackInputElement hok hgLex hbSz hderB with ⟨hnot, _⟩ | ⟨_, c', hc', dt', hpl', hhas'⟩
                · rw [hisTokB] at hnot; cases hnot
                · have hbLeJ := hclsUbJ c' hc' b dt' hpl'
                  have hbEqJ : b = j := by omega
                  subst hbEqJ
                  have hc'Eq : c' = .NumericLiteral := (hclsUniqAtJ c' hc' dt' hpl').trans hclsEqNum
                  subst hc'Eq; simp only [beq_self_eq_true] at hhas'
                  have hjLtLen : j < cs.toList.length := by
                    rw [Array.length_toList]; exact (Array.getElem?_eq_some_iff.mp hcj).1
                  obtain ⟨nFol, hnFolMem, tFol, hdFol⟩ := (follow_check_iff hok hcj).mp hfol
                  exact hnoFolB hhas' hjLtLen nFol hnFolMem ⟨tFol, hdFol⟩
              · simp only [hfol, Bool.false_eq_true, ↓reduceIte] at hr5
                obtain ⟨hEq, _⟩ := sm_pure_ok hr5
                cases hEq.symm
                dsimp only
                obtain ⟨tree0, hder0, hisTok0, hhas0⟩ := packToken hok hgLex hclsMem hkLe hplCls0
                have hmax0 : ∀ h, j < h → h ≤ cs.toList.length → ¬ ∃ t, LexDerives cx cs g [] sk.1 h t := by
                  intro h hjh hhLen ⟨t, hdt⟩
                  have hhSz : h ≤ cs.size := by simpa using hhLen
                  have hisTokH := stepTrivia_none_no_nontoken hok hcp hstNone hgLex hgb hhSz hdt
                  rcases unpackInputElement hok hgLex hhSz hdt with ⟨hnot, _⟩ | ⟨_, c', hc', dt', hpl', _⟩
                  · rw [hisTokH] at hnot; cases hnot
                  · have := hclsUbJ c' hc' h dt' hpl'; omega
                have hnoFol0 : tree0.has .NumericLiteral sk.1 j = true → j < cs.toList.length →
                    ∀ n ∈ [NT.IdentifierStart, NT.DecimalDigit], ¬ ∃ t, LexDerives cx cs n [] j (j + 1) t := by
                  intro _ _ n hn ⟨tF, hdF⟩
                  exact hfol ((follow_check_iff hok hcj).mpr ⟨n, hn, tF, hdF⟩)
                have hscan0 : ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal i sk.1 j sk.2 tree0 :=
                  ⟨htrSkip, hkLtJ, by simpa using hjSz, hisTok0, hder0, hmax0, hnoFol0⟩
                refine ⟨rfl, rfl, hik, hkLtJ, hjSz, ⟨tree0, hscan0, hhas0⟩, fun a b lt0 tr hscan => ?_⟩
                obtain ⟨htrA, _, hbLen, _, hderB, hmaxB, _⟩ := hscan
                obtain ⟨rfl, rfl⟩ := trivia_unique hok hcp htrSkip htrA
                have hbSz : b ≤ cs.size := by simpa using hbLen
                have hisTokB := stepTrivia_none_no_nontoken hok hcp hstNone hgLex hgb hbSz hderB
                rcases unpackInputElement hok hgLex hbSz hderB with ⟨hnot, _⟩ | ⟨_, c', hc', dt', hpl', _⟩
                · rw [hisTokB] at hnot; cases hnot
                · have hbLeJ := hclsUbJ c' hc' b dt' hpl'
                  have hjLeB : j ≤ b := Classical.byContradiction fun hgt =>
                    hmaxB j (by omega) (by simpa using hjSz) ⟨tree0, hder0⟩
                  exact ⟨rfl, by omega, rfl⟩
          · -- `cls != .NumericLiteral`
            have hclsNumF : (cls == .NumericLiteral) = false := Bool.eq_false_iff.mpr hclsNum
            simp only [hclsNumF, Bool.false_eq_true, ↓reduceIte] at hr5
            obtain ⟨hEq, _⟩ := sm_pure_ok hr5
            cases hEq.symm
            dsimp only
            obtain ⟨tree0, hder0, hisTok0, hhas0⟩ := packToken hok hgLex hclsMem hkLe hplCls0
            rw [hclsNumF] at hhas0
            have hmax0 : ∀ h, j < h → h ≤ cs.toList.length → ¬ ∃ t, LexDerives cx cs g [] sk.1 h t := by
              intro h hjh hhLen ⟨t, hdt⟩
              have hhSz : h ≤ cs.size := by simpa using hhLen
              have hisTokH := stepTrivia_none_no_nontoken hok hcp hstNone hgLex hgb hhSz hdt
              rcases unpackInputElement hok hgLex hhSz hdt with ⟨hnot, _⟩ | ⟨_, c', hc', dt', hpl', _⟩
              · rw [hisTokH] at hnot; cases hnot
              · have := hclsUbJ c' hc' h dt' hpl'; omega
            have hscan0 : ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first goal i sk.1 j sk.2 tree0 :=
              ⟨htrSkip, hkLtJ, by simpa using hjSz, hisTok0, hder0, hmax0, fun hh => by rw [hhas0] at hh; cases hh⟩
            refine ⟨rfl, rfl, hik, hkLtJ, hjSz, ⟨tree0, hscan0, hhas0.trans hclsNumF.symm⟩, fun a b lt0 tr hscan => ?_⟩
            obtain ⟨htrA, _, hbLen, _, hderB, hmaxB, _⟩ := hscan
            obtain ⟨rfl, rfl⟩ := trivia_unique hok hcp htrSkip htrA
            have hbSz : b ≤ cs.size := by simpa using hbLen
            have hisTokB := stepTrivia_none_no_nontoken hok hcp hstNone hgLex hgb hbSz hderB
            rcases unpackInputElement hok hgLex hbSz hderB with ⟨hnot, _⟩ | ⟨_, c', hc', dt', hpl', _⟩
            · rw [hisTokB] at hnot; cases hnot
            · have hbLeJ := hclsUbJ c' hc' b dt' hpl'
              have hjLeB : j ≤ b := Classical.byContradiction fun hgt =>
                hmaxB j (by omega) (by simpa using hjSz) ⟨tree0, hder0⟩
              exact ⟨rfl, by omega, rfl⟩

/-! ### Lexical goal agreement at non-`/` non-`}` tokens & token/trivia disjointness -/

private def nonCommonStartOk (s : Src) : Bool :=
  match s.alt.rhs with
  | .sym (.t (.text str _)) false :: _ =>
    match str.toList with
    | '/' :: _ | '}' :: _ => true
    | _ => false
  | _ => false

private def nonCommonNTs : List NT :=
  [.DivPunctuator, .RegularExpressionLiteral, .RightBracePunctuator, .TemplateMiddle, .TemplateTail]

private def nonCommonCert : Bool :=
  nonCommonNTs.all fun n =>
    (glData.alts cxHtmlFalse .lexical n).all nonCommonStartOk &&
    (glData.alts cxHtmlTrue .lexical n).all nonCommonStartOk

private theorem nonCommonCert_true : nonCommonCert = true := by decide

private theorem nonCommon_starts_slash_or_brace (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    {cls : NT} (hcls : cls ∈ nonCommonNTs) {a h : Nat} {dt : DTree}
    (hd : (lexSpec cs cx).PlainDerives cls [] a h dt) :
    cs[a]? = some 0x2F ∨ cs[a]? = some 0x7D := by
  obtain ⟨haltsF, haltsT⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp nonCommonCert_true cls hcls)
  cases hd with
  | node s hs _ _ _ hsw =>
    have hsMem := lex_mem_alts hok hs
    rw [alts_lexical_eq] at hsMem
    have hsOk : nonCommonStartOk s = true := by
      cases hht : Lex.html cx with
      | false => rw [hht] at hsMem; exact List.all_eq_true.mp haltsF s hsMem
      | true => rw [hht] at hsMem; exact List.all_eq_true.mp haltsT s hsMem
    unfold nonCommonStartOk at hsOk
    generalize hrhs : s.alt.rhs = rhs0 at hsOk hsw
    cases rhs0 with
    | nil => cases hsOk
    | cons it rest =>
      cases it with
      | sym sym0 o =>
        cases sym0 with
        | nt _ _ => cases o <;> cases hsOk
        | t tx =>
          cases o with
          | true => cases tx <;> cases hsOk
          | false =>
            cases tx with
            | cp _ => cases hsOk
            | text str b0 =>
              dsimp only at hsOk
              cases hchars : str.toList with
              | nil => rw [hchars] at hsOk; cases hsOk
              | cons ch chRest =>
                rw [hchars] at hsOk
                cases hsw with
                | term ht _ =>
                  have hw : str.toList.map Char.toNat = ch.toNat :: chRest.map Char.toNat := by
                    rw [hchars]; rfl
                  obtain ⟨_, hg0, _⟩ := termEnd_text_cons hw ht
                  by_cases h1 : ch = '/'
                  · subst h1; exact Or.inl hg0
                  · by_cases h2 : ch = '}'
                    · subst h2; exact Or.inr hg0
                    · simp [h1, h2] at hsOk
      | _ => cases hsOk

private theorem synLexGoal_common_mem {g1 g2 cls : NT}
    (hg1 : isSynLexGoal g1 = true) (_hg2 : isSynLexGoal g2 = true)
    (hm : cls ∈ Lex.classes g1) (hnot : cls ∉ nonCommonNTs) :
    cls ∈ Lex.classes g2 := by
  unfold isSynLexGoal at hg1
  simp only [Bool.or_eq_true, beq_iff_eq] at hg1
  unfold Lex.classes at hm ⊢
  rw [List.mem_append] at hm ⊢
  rcases hm with hcom | hrest
  · exact Or.inl hcom
  · exfalso; apply hnot
    rcases hg1 with (rfl | rfl) | rfl <;> (
      dsimp only at hrest
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrest
      try (rcases hrest with rfl | rfl <;> decide)
      try (rcases hrest with rfl | rfl | rfl <;> decide))

/-- At any token starting with neither `/` (`0x2F`) nor `}` (`0x7D`), all syntactic lexical goals
(`InputElementDiv`, `InputElementRegExp`, `InputElementTemplateTail`) scan the exact same token. -/
theorem scanTok_agree_not_slash_brace (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {g1 g2 : NT}
    (hg1 : isSynLexGoal g1 = true) (hg2 : isSynLexGoal g2 = true)
    {p a b : Nat} {lt : Bool} {tr1 : Tree}
    (hnot : cs[a]? ≠ some 0x2F ∧ cs[a]? ≠ some 0x7D)
    (hscan : ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first g1 p a b lt tr1) :
    ∃ tr2, ScanTok Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first g2 p a b lt tr2 := by
  obtain ⟨htr, hab, hbLen, hisTok1, hder1, hmax1, hfol1⟩ := hscan
  by_cases hfa : (first && a == 0) = true
  · refine ⟨tr1, htr, hab, hbLen, ?_⟩
    simp only [hfa, ↓reduceIte] at hisTok1 hder1 hmax1 ⊢
    exact ⟨hisTok1, hder1, hmax1, hfol1⟩
  · simp only [hfa, Bool.false_eq_true, ↓reduceIte] at hisTok1 hder1 hmax1
    have hbSz : b ≤ cs.size := by simpa using hbLen
    have haLe : a ≤ cs.size := by omega
    have hskEq : Lex.skip Engine.builder cs first cx p = (a, lt) := (trivia_eq_skip hok hcp).mp htr
    have hstNone : stepTrivia cs first cx a = none := by
      have ⟨_, _, hst, _, _⟩ := skip_spec (cx := cx) hok hcp first p
      rwa [hskEq] at hst
    have hg1L := isLexGoal_of_isSynLexGoal hg1
    have hg2L := isLexGoal_of_isSynLexGoal hg2
    rcases unpackInputElement hok hg1L hbSz hder1 with ⟨hnotT, _⟩ | ⟨_, cls, hcls1, dtCls, hplCls, hhas1⟩
    · rw [hisTok1] at hnotT; cases hnotT
    · have hclsNot : cls ∉ nonCommonNTs := fun hmem => by
        rcases nonCommon_starts_slash_or_brace hok hmem hplCls with h2f | h7d
        · exact hnot.1 h2f
        · exact hnot.2 h7d
      have hcls2 : cls ∈ Lex.classes g2 := synLexGoal_common_mem hg1 hg2 hcls1 hclsNot
      obtain ⟨tr2, hder2, hisTok2, hhas2⟩ := packToken hok hg2L hcls2 haLe hplCls
      refine ⟨tr2, htr, hab, hbLen, ?_⟩
      simp only [hfa, Bool.false_eq_true, ↓reduceIte]
      refine ⟨hisTok2, hder2, fun h hbh hhLen ⟨t', hdt'⟩ => ?_, ?_⟩
      · have hhSz : h ≤ cs.size := by simpa using hhLen
        have hgb2 : g2 = .InputElementHashbangOrRegExp → first = true ∧ a = 0 := fun heq => by
          rw [heq] at hg2; cases hg2
        have hisTok' := stepTrivia_none_no_nontoken hok hcp hstNone hg2L hgb2 hhSz hdt'
        rcases unpackInputElement hok hg2L hhSz hdt' with ⟨hn', _⟩ | ⟨_, cls', hcls2', dt', hpl', _⟩
        · rw [hisTok'] at hn'; cases hn'
        · have hclsNot' : cls' ∉ nonCommonNTs := fun hmem => by
            rcases nonCommon_starts_slash_or_brace hok hmem hpl' with h2f | h7d
            · exact hnot.1 h2f
            · exact hnot.2 h7d
          have hcls1' : cls' ∈ Lex.classes g1 := synLexGoal_common_mem hg2 hg1 hcls2' hclsNot'
          obtain ⟨tr1', hder1', _, _⟩ := packToken hok hg1L hcls1' haLe hpl'
          exact hmax1 h hbh hhLen ⟨tr1', hder1'⟩
      · rw [hhas2, ← hhas1]
        exact hfol1

/-- A maximal token element under a valid lexical goal at `a` precludes any `TriviaElem` starting at `a`. -/
theorem no_triviaElem_at_max_token (hok : parseTablesOk = true) {cx : Ctx} {cs : Array Nat}
    (hcp : ∀ c ∈ cs.toList, c ≤ 0x10FFFF) {first : Bool} {g : NT} {a b : Nat}
    (hg : isLexGoal g = true)
    (hfb : (first && a == 0) = true → g = .InputElementHashbangOrRegExp)
    (hab : a < b) (hb : b ≤ cs.size) {tr : Tree}
    (hisTok : Element.isToken ⟨a, b, g, tr⟩ = true)
    (hder : LexDerives cx cs g [] a b tr)
    (hmax : ∀ h, b < h → h ≤ cs.toList.length → ¬ ∃ t, LexDerives cx cs g [] a h t) :
    ¬ ∃ m e', TriviaElem Ecma.Spec.gl cx Engine.Model.codePrims cs.toList first a m e' := by
  rcases hst : stepTrivia cs first cx a with _ | ⟨m, l⟩
  · exact stepTrivia_none_no_triviaElem hok hcp hst
  · intro _
    have haLe : a ≤ cs.size := Nat.le_of_lt (Nat.lt_of_lt_of_le hab hb)
    rcases unpackInputElement hok hg hb hder with ⟨hnotT, _⟩ | ⟨_, cls, hcls, dt, hpl, _⟩
    · rw [hisTok] at hnotT; cases hnotT
    · have ⟨_, ⟨ca, hca, hnws, hnlt⟩, _, _, _, hslash, hhash, hlt3c, hdash⟩ :=
        tokLead_props hok (sizeOf dt) (Nat.le_refl _)
          (List.mem_append_left _ (classes_sub_allTokClasses g cls hcls)) haLe hpl
      obtain ⟨_, hmSz, ⟨e0, hte0, _, _⟩, _⟩ := stepTrivia_some_spec hok hcp hst
      obtain ⟨_, _, _, _, hnotTok0, hegoal0, hder0, _⟩ := hte0
      let g0 : NT := if first && a == 0 then .InputElementHashbangOrRegExp else .InputElementDiv
      have hg0 : isLexGoal g0 = true := by dsimp only [g0]; split <;> decide
      have hder0' : LexDerives cx cs g0 [] a m e0.tree := by rw [hegoal0] at hder0; exact hder0
      have hisTok0F : Element.isToken ⟨a, m, g0, e0.tree⟩ = false :=
        Bool.eq_false_iff.mpr fun h => by
          rw [show Element.isToken e0 = Element.isToken ⟨a, m, g0, e0.tree⟩ from rfl, h] at hnotTok0
          cases hnotTok0
      rcases unpackInputElement hok hg0 hmSz hder0' with ⟨_, _, hnt⟩ | ⟨hisT0, _⟩
      · rcases hnt with ⟨_, _, hdW⟩ | ⟨_, _, hdL⟩ | ⟨_, dtC, hdC⟩ | ⟨_, _, _, hdHB⟩ | ⟨hg0Eq, hht, _, dtHC, hdHC⟩
        · obtain ⟨c', hc', hws', _⟩ := (whiteSpace_iff hok).mp ⟨_, hdW⟩
          rw [hca] at hc'; injection hc' with he; subst he; rw [hnws] at hws'; cases hws'
        · obtain ⟨c', hc', hlt', _⟩ := (lineTerminator_iff hok).mp ⟨_, hdL⟩
          rw [hca] at hc'; injection hc' with he; subst he; rw [hnlt] at hlt'; cases hlt'
        · rcases (comment_iff hok hcp).mp ⟨dtC, hdC⟩ with
            ⟨hg0', hg1', ha2m, _⟩ | ⟨hg0', hg1', cCl, hcl, _⟩ |
            ⟨_, hg0', hg1', _, _, ha4m, _⟩ | ⟨_, c', hc', hlt', _⟩
          · obtain ⟨treeC, hderC, _, _, _⟩ := packNonToken hok hg haLe (Or.inr (Or.inr (Or.inl rfl))) hdC
            have hb1 := hslash hg0' (Or.inl hg1')
            exact hmax m (by omega) (by simpa using hmSz) ⟨treeC, hderC⟩
          · have hb1 := hslash hg0' (Or.inr hg1')
            obtain ⟨ha2c, hc1Lt, _, _, _⟩ := closeAt_some_spec cs (a + 2) cCl hcl
            obtain ⟨dtCM, hdCM⟩ := (comment_iff (cx := cx) hok hcp).mpr
              (Or.inr (Or.inl ⟨hg0', hg1', cCl, hcl, Or.inl rfl⟩))
            obtain ⟨treeCM, hderCM, _, _, _⟩ := packNonToken hok hg haLe (Or.inr (Or.inr (Or.inl rfl))) hdCM
            exact hmax (cCl + 2) (by omega) (by rw [Array.length_toList]; omega) ⟨treeCM, hderCM⟩
          · obtain ⟨treeC, hderC, _, _, _⟩ := packNonToken hok hg haLe (Or.inr (Or.inr (Or.inl rfl))) hdC
            have hb1 := hlt3c hg0' hg1'
            exact hmax m (by omega) (by simpa using hmSz) ⟨treeC, hderC⟩
          · rw [hca] at hc'; injection hc' with he; subst he; rw [hnlt] at hlt'; cases hlt'
        · obtain ⟨hg0', hg1', _⟩ := (hashbangComment_iff hok hcp).mp ⟨_, hdHB⟩
          exact absurd hg1' (hhash hg0')
        · have hfa : (first && a == 0) = true := by
            dsimp only [g0] at hg0Eq
            by_cases hif : (first && a == 0) = true
            · exact hif
            · simp [hif] at hg0Eq
          obtain ⟨_, ha0⟩ : first = true ∧ a = 0 := by simpa [Bool.and_eq_true, beq_iff_eq] using hfa
          subst ha0
          have hgEq := hfb hfa
          rcases hhc0 : Lex.htmlClose Engine.builder cs 0 with _ | ehc0
          · exact absurd hdHC ((htmlClose_spec hok hcp hht 0).2 hhc0 m dtHC)
          · obtain ⟨h3ehc, hehcSz, ⟨dtHC0, hdHC0⟩, _⟩ := (htmlClose_spec hok hcp hht 0).1 ehc0 hhc0
            obtain ⟨treeHC, hderHC, _, _, _⟩ := packNonToken hok hg haLe
              (Or.inr (Or.inr (Or.inr (Or.inr ⟨hgEq, hht, rfl⟩)))) hdHC0
            have hbehc : b < ehc0 := by
              have ⟨_, _, hwAll, _⟩ := wsEnd_spec cs 0
              by_cases hwpos : 0 < Lex.wsEnd Engine.builder cs 0
              · obtain ⟨c', hc', hws'⟩ := hwAll 0 (Nat.le_refl _) hwpos
                rw [hca] at hc'; injection hc' with he; subst he; rw [hnws] at hws'; cases hws'
              · have hw0 : Lex.wsEnd Engine.builder cs 0 = 0 := by omega
                have hhcU := hhc0
                unfold Lex.htmlClose at hhcU; dsimp only at hhcU
                rw [hw0] at hhcU; simp only [Nat.zero_add] at hhcU
                rcases hg0' : cs[0]? with _ | cw0; · rw [hg0'] at hhcU; cases hhcU
                rw [hg0'] at hhcU
                by_cases h2d : cw0 = 0x2D
                · subst h2d
                  rcases hg1' : cs[1]? with _ | cw1; · rw [hg1'] at hhcU; cases hhcU
                  rw [hg1'] at hhcU
                  by_cases h2d1 : cw1 = 0x2D
                  · subst h2d1
                    rcases hg2' : cs[2]? with _ | cw2; · rw [hg2'] at hhcU; cases hhcU
                    rw [hg2'] at hhcU
                    by_cases h3e' : cw2 = 0x3E
                    · subst h3e'; have := hdash hg0' hg1' hg2'; omega
                    · simp [h3e'] at hhcU
                  · simp [h2d1] at hhcU
                · by_cases h2f : cw0 = 0x2F
                  · subst h2f
                    rcases hg1' : cs[1]? with _ | cw1; · rw [hg1'] at hhcU; cases hhcU
                    rw [hg1'] at hhcU
                    by_cases h2a : cw1 = 0x2A
                    · subst h2a; have := hslash hg0' (Or.inr hg1'); omega
                    · simp [h2a] at hhcU
                  · simp [h2d, h2f] at hhcU
            exact hmax ehc0 hbehc (by simpa using hehcSz) ⟨treeHC, hderHC⟩
      · rw [hisTok0F] at hisT0; cases hisT0

end Engine.Parse
