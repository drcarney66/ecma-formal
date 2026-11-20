module

public import Engine.Model.CharSet
public import Engine.Proofs.Unicode
public import Engine.Proofs.Seq
public import Engine.Proofs.Maps

@[expose] public section

/-!
# Shared sequence, code-point, and `CharSet` membership helpers
-/

namespace Engine.Impl

open Ecma Engine.Model

theorem isPoint_iff (m : MathVal) : Model.isPoint Impl m ↔ ∃ c : Nat, c ≤ maxCodePoint ∧ m = .int c := by
  constructor
  · rintro ⟨hi, h0, h1⟩
    cases m with
    | frac _ _ => cases hi
    | int j =>
      have hj0 : 0 ≤ j := by
        change decide (j < (0 : Int)) = false at h0
        have := of_decide_eq_false h0; omega
      have hj1 : j ≤ (maxCodePoint : Int) := by
        change decide ((1114111 : Int) < j) = false at h1
        have := of_decide_eq_false h1
        unfold maxCodePoint; omega
      exact ⟨j.toNat, by omega, by congr 1; exact (Int.toNat_of_nonneg hj0).symm⟩
  · rintro ⟨c, hc, rfl⟩; exact nat_isPoint c hc

theorem point?_eq_some (m : MathVal) (c : Nat) : point? m = some c ↔ c ≤ maxCodePoint ∧ m = .int c := by
  cases m with
  | frac _ _ => exact ⟨fun h => by simp [point?] at h, fun ⟨_, h⟩ => by cases h⟩
  | int j =>
    unfold point?
    constructor
    · intro h
      by_cases hle : 0 ≤ j ∧ j ≤ (maxCodePoint : Int)
      · simp [hle] at h; subst h; exact ⟨by omega, by congr 1; exact (Int.toNat_of_nonneg hle.1).symm⟩
      · simp [hle] at h
    · rintro ⟨hc, he⟩; cases he
      have h1 : (0 : Int) ≤ (c : Int) := Int.natCast_nonneg c
      have h2 : (c : Int) ≤ (maxCodePoint : Int) := Int.ofNat_le.2 hc
      simp [h1, h2]

theorem mapM_point?_eq {l : List MathVal} {pts : List Nat} (h : l.mapM point? = some pts) :
    l = pts.map (fun c : Nat => MathVal.int c) ∧ ∀ c ∈ pts, c ≤ maxCodePoint := by
  induction l generalizing pts with
  | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; simp
  | cons x r ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨c, hc, cs, hcs, rfl⟩ := h
    obtain ⟨hcLe, hx⟩ := (point?_eq_some x c).1 hc
    subst hx
    have ⟨hl, hall⟩ := ih hcs
    exact ⟨by simp [hl], fun d hd => (List.mem_cons.1 hd).elim (fun h => h ▸ hcLe) (hall d)⟩

theorem mapM_point?_of (pts : List Nat) (hle : ∀ c ∈ pts, c ≤ maxCodePoint) :
    (pts.map (fun c : Nat => MathVal.int c)).mapM point? = some pts := by
  induction pts with
  | nil => rfl
  | cons c r ih =>
    simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.pure_def]
    rw [(point?_eq_some (.int c) c).2 ⟨hle c (by simp), rfl⟩]
    simp [ih fun d hd => hle d (List.mem_cons_of_mem _ hd)]

theorem allPoints_iff (s : Array MathVal) :
    Model.allPoints Impl s ↔ ∃ pts : List Nat, s.toList.mapM point? = some pts := by
  constructor
  · intro hs
    have hall : ∀ x ∈ s.toList, ∃ c : Nat, c ≤ maxCodePoint ∧ x = .int c := fun x hx => by
      obtain ⟨k, hk, he⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hx)
      exact (isPoint_iff x).1 (hs (.int k) x (by rw [seqGet_nat, Array.getElem?_eq_getElem hk, he]))
    suffices ∀ l : List MathVal, (∀ x ∈ l, ∃ c : Nat, c ≤ maxCodePoint ∧ x = .int c) →
        ∃ pts : List Nat, l.mapM point? = some pts from this s.toList hall
    intro l hl; induction l with
    | nil => exact ⟨[], rfl⟩
    | cons x r ih =>
      obtain ⟨c, hc, rfl⟩ := hl x (by simp)
      obtain ⟨pts, hp⟩ := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
      exact ⟨c :: pts, by simp [List.mapM_cons, (point?_eq_some (.int c) c).2 ⟨hc, rfl⟩, hp]⟩
  · rintro ⟨pts, hp⟩
    obtain ⟨hs, hle⟩ := mapM_point?_eq hp
    apply allPoints_of
    intro x hx; rw [hs] at hx; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx; exact ⟨c, hle c hc, rfl⟩

theorem csHas_iff_mem (cs : CharSet) (pts : List Nat) (hle : ∀ c ∈ pts, c ≤ maxCodePoint)
    {s : Array MathVal} (hs : s.toList = pts.map (fun c : Nat => MathVal.int c)) :
    Impl.csHas cs s = true ↔
      (∃ c, pts = [c] ∧ MemRanges cs.ranges.toList c) ∨ (pts.length ≠ 1 ∧ (cs.strings.get pts).isSome = true) := by
  change Engine.Model.csHas cs s = true ↔ _
  unfold Engine.Model.csHas
  rw [hs, mapM_point?_of pts hle]
  cases pts with
  | nil => simp
  | cons c r =>
    cases r with
    | nil => simp [csHasChar, inRangesA_iff cs.ranges cs.hr c]
    | cons _ _ => simp

theorem hasChar_iff (cs : CharSet) (x : Nat) (hx : x ≤ maxCodePoint) :
    csHasChar cs x = true ↔ Impl.csHas cs (Impl.seqPush Impl.seqNil (.int x)) = true := by
  have hs : (Impl.seqPush Impl.seqNil (.int x)).toList = ([x].map fun c : Nat => MathVal.int c) := rfl
  rw [csHas_iff_mem cs [x] (fun _ hm => by simp at hm; subst hm; exact hx) hs]
  simp [csHasChar, inRangesA_iff cs.ranges cs.hr x]

theorem wmap_empty_get (k : List Nat) : (WMap.empty : StrMap).get k = none := by
  simp [WMap.get, WMap.empty, OMap.empty, OMap.get]

end Engine.Impl
