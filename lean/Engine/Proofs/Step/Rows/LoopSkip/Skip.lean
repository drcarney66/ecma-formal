module

public import Engine.Proofs.Step.Rows.LoopSkip.Round

@[expose] public section

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel

/-! ## What the skip computed -/

theorem ls_find_range (q : Nat → Bool) : ∀ n : Nat, ((List.range n).find? q).getD n ≤ n ∧
    ∀ j < ((List.range n).find? q).getD n, q j = false := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.find?_append]
    cases h : (List.range n).find? q with
    | some d =>
      simp only [h, Option.getD_some] at ih
      simp only [Option.some_or, Option.getD_some]
      exact ⟨by omega, ih.2⟩
    | none =>
      simp only [h, Option.getD_none] at ih
      simp only [Option.none_or, List.find?_cons, List.find?_nil]
      cases hq : q n with
      | true => simpa using ih.2
      | false =>
        simp only [Option.getD_none]
        refine ⟨Nat.le_refl _, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
        · exact ih.2 j h'
        · exact hq

theorem ls_probe (ch : List (F.Props (Val F))) (desc : Bool) (i n : Nat) : probe ch desc i n ≤ n ∧
    ∀ j < probe ch desc i n, chainHas ch (if desc then i - j else i + j) = false :=
  ls_find_range (fun d => chainHas ch (if desc then i - d else i + d)) n

/-- The rounds the skip takes, from the chain's keys: `skipRun`'s `g`. -/
def lsG (ch : List (F.Props (Val F))) (desc : Bool) (i lim : Nat) : Nat :=
  let n := min (probeLimit + 1) lim
  let d := probe ch desc i n
  if d < n || n == lim then d
  else if (ch.map propsSize).sum ≤ keyLimit then min lim ((nearestKey ch desc i probeLimit).getD lim)
  else n

/-- The skip's answer at the index `i` and `g` rounds: `skipRun`'s. -/
def lsOut (m : LoopSlots) (i g : Nat) : Run F (Nat × List (Slot × Val F)) :=
  let last := if m.desc then i - (g - 1) else i + (g - 1)
  fun st => .ok (g, [(m.k, .math (.int (if m.desc then (i : Int) - g else i + g))),
      (m.pk, .str (F.strLit (toString last))), (m.kp, .bool false)]) st

theorem ls_guard_pos {p : Prop} [Decidable p] (h : p) : (guard p : Option Unit) = some () := by
  simp [guard, h]

theorem ls_guard_neg {p : Prop} [Decidable p] (h : ¬ p) : (guard p : Option Unit) = none := by
  simp only [guard, h, ↓reduceIte]
  rfl

/-- `skipRun` from its rounds' limit. -/
def lsTail (m : LoopSlots) (s : State F) (ad : Nat) (i lim : Nat) : Option (Run F (Nat × List (Slot × Val F))) := do
  guard (0 < lim)
  let ch ← ordChain s chainLimit ad
  let n := min (probeLimit + 1) lim
  let d := probe ch m.desc i n
  guard (0 < d)
  let g := if d < n || n == lim then d
    else if (ch.map propsSize).sum ≤ keyLimit then min lim ((nearestKey ch m.desc i probeLimit).getD lim)
    else n
  let last := if m.desc then i - (g - 1) else i + (g - 1)
  some fun st => .ok (g, [(m.k, .math (.int (if m.desc then (i : Int) - g else i + g))),
      (m.pk, .str (F.strLit (toString last))), (m.kp, .bool false)]) st

theorem ls_tail {m : LoopSlots} {s : State F} {ad i lim : Nat} {run : Run F (Nat × List (Slot × Val F))}
    (h : lsTail m s ad i lim = some run) :
    0 < lim ∧ ∃ ch, ordChain s chainLimit ad = some ch ∧ 0 < probe ch m.desc i (min (probeLimit + 1) lim) ∧
      run = lsOut m i (lsG ch m.desc i lim) := by
  unfold lsTail at h
  by_cases h1 : 0 < lim
  · refine ⟨h1, ?_⟩
    cases hch : ordChain s chainLimit ad with
    | none => simp [guard, h1, hch, bind] at h
    | some ch =>
      by_cases h2 : 0 < probe ch m.desc i (min (probeLimit + 1) lim)
      · refine ⟨ch, rfl, h2, ?_⟩
        simp only [guard, h1, hch, bind, Option.bind, ↓reduceIte, pure, h2] at h
        exact (Option.some.inj h).symm
      · simp only [guard, h1, hch, bind, Option.bind, ↓reduceIte, pure, h2, failure, Alternative.failure] at h
        cases h
  · simp only [guard, h1, bind, Option.bind, ↓reduceIte, failure, Alternative.failure] at h
    cases h

/-- What `skipRun` read and checked where it answers. -/
theorem ls_skip (m : LoopSlots) (sl : Array (Val F)) (s : State F) (run : Run F (Nat × List (Slot × Val F)))
    (h : skipRun m none sl s = some run) :
    ∃ (i : Int) (ad : Nat) (lim : Nat) (ch : List (F.Props (Val F))),
      sl[m.k]? = some (.math (.int i)) ∧ sl[m.o]? = some (.obj ad) ∧ 0 ≤ i ∧ i < 2 ^ 53 ∧ m.pk < sl.size ∧
      m.kp < sl.size ∧
      (match m.bound with
        | some b => ∃ len : Int, sl[b]? = some (.math (.int len)) ∧
          lim = (min len (2 ^ 53) - ((i.toNat : Nat) : Int)).toNat
        | none => lim = i.toNat + 1) ∧
      0 < lim ∧ ordChain s chainLimit ad = some ch ∧ 0 < probe ch m.desc i.toNat (min (probeLimit + 1) lim) ∧
      run = lsOut m i.toNat (lsG ch m.desc i.toNat lim) := by
  unfold skipRun at h
  simp (config := { zeta := false }) only [bind, Option.bind] at h
  cases hk : sl[m.k]? with
  | none => rw [hk] at h; cases h
  | some v =>
    rw [hk] at h
    cases v <;> try (cases h; done)
    rename_i x
    cases x <;> try (cases h; done)
    rename_i i
    simp (config := { zeta := false }) only [] at h
    cases ho : sl[m.o]? with
    | none => rw [ho] at h; cases h
    | some v =>
      rw [ho] at h
      cases v <;> try (cases h; done)
      rename_i ad
      simp (config := { zeta := false }) only [] at h
      by_cases hg : (decide (0 ≤ i) && decide (i < 2 ^ 53) && decide (m.pk < sl.size) && decide (m.kp < sl.size)) = true
      · rw [ls_guard_pos hg] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hg
        cases hb : m.bound with
        | none =>
          rw [hb] at h
          have h' : lsTail m s ad i.toNat (i.toNat + 1) = some run := h
          obtain ⟨hl, ch, hch, hp, hr⟩ := ls_tail h'
          exact ⟨i, ad, i.toNat + 1, ch, rfl, rfl, g1, g2, g3, g4, rfl, hl, hch, hp, hr⟩
        | some b =>
          rw [hb] at h
          simp (config := { zeta := false }) only [] at h
          cases hl : sl[b]? with
          | none => rw [hl] at h; cases h
          | some v =>
            rw [hl] at h
            cases v <;> try (cases h; done)
            rename_i x
            cases x <;> try (cases h; done)
            rename_i len
            have h' : lsTail m s ad i.toNat (min len (2 ^ 53) - ((i.toNat : Nat) : Int)).toNat = some run := h
            obtain ⟨hl', ch, hch, hp, hr⟩ := ls_tail h'
            exact ⟨i, ad, _, ch, rfl, rfl, g1, g2, g3, g4, ⟨len, hl, rfl⟩, hl', hch, hp, hr⟩
      · rw [ls_guard_neg hg] at h
        cases h


/-- What the skip needs of `nearestKey`: its answer lies past the probed indices, and no index key of the chain past
them lies nearer. -/
def LsNearest (ch : List (F.Props (Val F))) (desc : Bool) (i : Nat) : Prop :=
  (∀ e, nearestKey ch desc i probeLimit = some e → probeLimit < e) ∧
    ∀ j : Nat, probeLimit < j → (desc = true → j ≤ i) →
      chainHas ch (if desc then i - j else i + j) = true → ∃ e, nearestKey ch desc i probeLimit = some e ∧ e ≤ j

/-- The skip's rounds: at least one, within the limit, at indices whose keys the chain lacks. -/
theorem ls_g {ch : List (F.Props (Val F))} {desc : Bool} {i lim : Nat} (hnear : LsNearest ch desc i)
    (hlim : 0 < lim) (hp : 0 < probe ch desc i (min (probeLimit + 1) lim)) (hdesc : desc = true → lim ≤ i + 1) :
    0 < lsG ch desc i lim ∧ lsG ch desc i lim ≤ lim ∧
      ∀ j < lsG ch desc i lim, chainHas ch (if desc then i - j else i + j) = false := by
  obtain ⟨hd, hab⟩ := ls_probe ch desc i (min (probeLimit + 1) lim)
  obtain ⟨na, nb⟩ := hnear
  have hpl : probeLimit = 64 := rfl
  unfold lsG
  simp only []
  split
  · rename_i hc
    exact ⟨hp, by omega, hab⟩
  · rename_i hc
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hdn : probe ch desc i (min (probeLimit + 1) lim) = probeLimit + 1 := by omega
    split
    · have key : ∀ j, j < lim → (∀ e, nearestKey ch desc i probeLimit = some e → j < e) →
          chainHas ch (if desc then i - j else i + j) = false := by
        intro j hj he
        by_cases hj' : j < probeLimit + 1
        · exact hab j (by omega)
        · cases hh : chainHas ch (if desc then i - j else i + j) with
          | false => rfl
          | true =>
            obtain ⟨e, he1, he2⟩ := nb j (by omega) (fun hd' => by have := hdesc hd'; omega) hh
            have := he e he1
            omega
      cases hn : nearestKey ch desc i probeLimit with
      | none =>
        simp only [Option.getD_none, Nat.min_self]
        exact ⟨hlim, Nat.le_refl _, fun j hj => key j hj (fun e he => by rw [hn] at he; cases he)⟩
      | some e =>
        have := na e hn
        simp only [Option.getD_some]
        refine ⟨by omega, by omega, fun j hj => key j (by omega) (fun e' he' => ?_)⟩
        rw [hn] at he'
        cases he'
        omega
    · exact ⟨by omega, by omega, fun j hj => hab j (by omega)⟩

end Engine.Machine
