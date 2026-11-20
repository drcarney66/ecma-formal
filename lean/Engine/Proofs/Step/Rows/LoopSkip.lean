module

public import Engine.Proofs.Step.Rows.LoopSkip.Round
public import Engine.Proofs.Step.Rows.LoopSkip.Skip
public import Engine.Proofs.Step.Rows.LoopSkip.Nearest

@[expose] public section

/-!
# The sparse HasProperty loop's skip

The engine's shortcut at the head of a `Repeat, while k < len` (or `k ≥ 0`) HasProperty loop
(`Engine.Accel.Table.loopRow`: `hasPropLoop`, `skipRun`) is the specification's steps: `loopSkip_row`, under
`LsIntKeys` (an arithmetic fact about the entry's `numberToStringLog` at integers below 2^53).

* `LoopSkip/Round.lean`: the callees' runs at an ordinary object without the key (`ls_toString`, `ls_ogop`,
  `ls_ordGop`, `ls_ogpo`, `ls_ordGpo`, `ls_ordHas`, `ls_hasProperty`), one round (`ls_round`), the rounds
  (`ls_rounds`).
* `LoopSkip/Skip.lean`: what `skipRun` read and computed (`ls_skip`, `ls_g`).
* `LoopSkip/Nearest.lean`: `nearestKey` is right (`ls_nearest`), the index of an index key (`ls_indexOf`).
-/

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel

variable (H : Host F) (rd : ErratumId → Reading) (chk : Bool)

set_option maxRecDepth 8000 in
/-- The skip's answer in the rounds' terms. -/
theorem ls_out_eq (m : LoopSlots) (i : Int) (g : Nat) (h0 : 0 ≤ i) (hd : m.bound = none → (g : Int) ≤ i) :
    lsOut m i.toNat (g + 1) = fun st => .ok (g + 1, [(m.k, .math (.int (lsStep m.bound i (g + 1)))),
      (m.pk, .str (lsKeyStr (lsStep m.bound i g))), (m.kp, .bool false)]) st := by
  obtain ⟨k, bound, o, pk, kp⟩ := m
  cases bound with
  | none =>
    have hd := hd rfl
    have e1 : ((i.toNat : Nat) : Int) - ((g + 1 : Nat) : Int) = i - ((g + 1 : Nat) : Int) := by omega
    have e2 : i.toNat - (g + 1 - 1) = (i - (g : Int)).toNat := by omega
    funext st
    simp only [lsOut, LoopSlots.desc, Option.isNone_none, ↓reduceIte, lsStep, lsKeyStr]
    rw [e1, e2]
  | some len =>
    have e1 : ((i.toNat : Nat) : Int) + ((g + 1 : Nat) : Int) = i + ((g + 1 : Nat) : Int) := by omega
    have e2 : i.toNat + (g + 1 - 1) = (i + (g : Int)).toNat := by omega
    funext st
    simp only [lsOut, LoopSlots.desc, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, lsStep, lsKeyStr]
    rw [e1, e2]

theorem ls_writeSlots (k pk kp : Slot) (sl : Array (Val F)) (key : F.Str) (k' : Int) (h1 : k ≠ pk) (h2 : k ≠ kp) :
    writeSlots (M := F) [(k, .math (.int k')), (pk, .str key), (kp, .bool false)] sl = lsPost k pk kp sl key k' := by
  apply Array.ext_getElem?
  intro y
  simp only [writeSlots, lsPost, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  grind

theorem ls_chainHas {ch : List (F.Props (Val F))} {n : Nat} (h : chainHas ch n = false) :
    lsNone ch (F.strLit (toString n)) := by
  intro ps hps
  simp only [chainHas, List.any_eq_false] at h
  have := h ps hps
  simpa [indexKey] using this


/-! ## Matching lowered code -/

theorem ls_eraseDups_le : ∀ (n : Nat) (l : List Nat), l.length ≤ n → l.eraseDups.length ≤ l.length := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons]
      have h1 := List.length_filter_le (fun b => !b == a) as
      have h2 := ih (as.filter fun b => !b == a) (by simp only [List.length_cons] at hl; omega)
      simp only [List.length_cons]
      omega

theorem ls_eraseDups_nodup : ∀ (n : Nat) (l : List Nat), l.length ≤ n → l.eraseDups.length = l.length →
    l.Nodup := by
  intro n
  induction n with
  | zero =>
    intro l hl _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp
  | succ n ih =>
    intro l hl h
    cases l with
    | nil => simp
    | cons a as =>
      rw [List.eraseDups_cons] at h
      simp only [List.length_cons] at h hl
      have h1 := List.length_filter_le (fun b => !b == a) as
      have h2 := ls_eraseDups_le n (as.filter fun b => !b == a) (by omega)
      have h3 : (as.filter fun b => !b == a).length = as.length := by omega
      have h4 : (as.filter fun b => !b == a) = as := by
        have := List.filter_sublist (p := fun b => !b == a) (l := as)
        exact this.eq_of_length h3
      rw [h4] at h
      refine List.nodup_cons.mpr ⟨?_, ih as (by omega) (by omega)⟩
      intro hm
      have := (List.filter_eq_self.mp h4) a hm
      simp at this

/-- A loop whose test and body match `hasPropLoop` has pairwise distinct slots and is `lsTest` and `lsBody`. -/
theorem ls_match (p : List Nat) (t : Op) (body : Code) (m : LoopSlots) (h : hasPropLoop p t body = some m) :
    t = lsTest m.k m.bound ∧ (∃ tb, body = lsBody p m.k m.o m.pk m.kp tb (lsUpd m.k m.bound)) ∧
      m.k ≠ m.pk ∧ m.k ≠ m.kp ∧ m.o ≠ m.k ∧ m.o ≠ m.pk ∧ m.o ≠ m.kp ∧ m.pk ≠ m.kp ∧
      ∀ len, m.bound = some len → len ≠ m.k ∧ len ≠ m.pk ∧ len ≠ m.kp := by
  unfold hasPropLoop at h
  split at h
  · rename_i p1 pk k1 p2 kp o pk1 p3 kp1 tb p4 k2 op k3
    dsimp only at h
    split at h
    · rename_i k0 len
      split at h
      · rename_i hk0
        simp only [Option.bind_some] at h
        split at h
        · rename_i hall
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq] at hall hk0
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hd⟩ := hall
          subst hk0
          have hnd := ls_eraseDups_nodup _ _ (Nat.le_refl _) hd
          dsimp only
          simp only [Option.toList, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
            List.not_mem_nil, or_false, not_or] at hnd
          refine ⟨rfl, ⟨tb, rfl⟩, ?_⟩
          grind
        · cases h
      · cases h
    · rename_i k0
      split at h
      · rename_i hk0
        simp only [Option.bind_some] at h
        split at h
        · rename_i hall
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq] at hall hk0
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hd⟩ := hall
          subst hk0
          have hnd := ls_eraseDups_nodup _ _ (Nat.le_refl _) hd
          dsimp only
          simp only [Option.toList, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
            List.not_mem_nil, or_false, not_or] at hnd
          refine ⟨rfl, ⟨tb, rfl⟩, ?_⟩
          grind
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## The row -/

set_option maxRecDepth 8000 in
/-- The skip at a loop whose test and body are `lsTest` and `lsBody` of the slots. -/
theorem ls_sim [PinsHold] (hkeys : LsIntKeys) (c : Cfg F) (back : Bool) (l : Loop F) (t : Op)
    (m : LoopSlots) (tb : Code) (run : Run F (Nat × List (Slot × Val F)))
    (hc : c.ctl = .loop (.spend back) l) (hit : l.it = .while_ t) (ht : t = lsTest m.k m.bound)
    (hbody : l.body = lsBody l.p m.k m.o m.pk m.kp tb (lsUpd m.k m.bound))
    (h1 : m.k ≠ m.pk) (h2 : m.k ≠ m.kp) (h3 : m.o ≠ m.k) (h4 : m.o ≠ m.pk) (h5 : m.o ≠ m.kp) (h6 : m.pk ≠ m.kp)
    (h7 : ∀ len, m.bound = some len → len ≠ m.k ∧ len ≠ m.pk ∧ len ≠ m.kp)
    (hrun : skipRun m none c.top.slots c.s = some run) :
    Sim (Ctx.spec Engine.P' H rd chk) c (bindR c run fun (g, ws) c =>
      loopTest (c.mapTop fun f => { f with slots := writeSlots ws f.slots }) { l with r := l.r + g + 1 } t) := by
  obtain ⟨s, frames, ctl⟩ := c
  obtain ⟨x, it, p, body, st, r⟩ := l
  cases hc
  cases hit
  have hbody : body = lsBody p m.k m.o m.pk m.kp tb (lsUpd m.k m.bound) := hbody
  subst hbody
  subst ht
  obtain ⟨i, ad, lim, ch, hk, ho, i0, i1, hpk, hkp, hlim, hl0, hch, hp, hr⟩ := ls_skip m _ s run hrun
  cases frames with
  | nil => simp [Cfg.top] at hk
  | cons f fs =>
    obtain ⟨a, nd, sl, kd, p', K, ci⟩ := f
    have hk : sl[m.k]? = some (.math (.int i)) := hk
    have ho : sl[m.o]? = some (.obj ad) := ho
    have hpk : m.pk < sl.size := hpk
    have hkp : m.kp < sl.size := hkp
    have hdesc : m.desc = true → lim ≤ i.toNat + 1 := by
      intro hd
      cases hb : m.bound with
      | none => rw [hb] at hlim; omega
      | some len => simp [LoopSlots.desc, hb] at hd
    obtain ⟨g0, g1, g2⟩ := ls_g (ls_nearest ch m.desc i.toNat) hl0 hp hdesc
    obtain ⟨g, hg⟩ : ∃ g, lsG ch m.desc i.toNat lim = g + 1 := ⟨_, (Nat.succ_pred_eq_of_pos g0).symm⟩
    rw [hg] at hr g1 g2
    have hd : m.bound = none → (g : Int) ≤ i := by
      intro hb
      rw [hb] at hlim
      omega
    rw [ls_out_eq m i g i0 hd] at hr
    subst hr
    have hslots : LsSlots m.k m.o m.pk m.kp m.bound sl ad := ⟨ho, hpk, hkp, h1, h2, h3, h4, h5, h6, h7⟩
    have hcond : lsCond m.bound sl i g := by
      cases hb : m.bound with
      | none => exact ⟨hd hb, i1⟩
      | some len =>
        rw [hb] at hlim
        obtain ⟨n, hn, hlim⟩ := hlim
        exact ⟨n, hn, by omega, by omega⟩
    have hno : ∀ j ≤ g, lsNone ch (lsKeyStr (lsStep m.bound i j)) := by
      intro j hj
      have := ls_chainHas (g2 j (by omega))
      have e : (if m.desc = true then i.toNat - j else i.toNat + j) = (lsStep m.bound i j).toNat := by
        cases hb : m.bound with
        | none =>
          have := hd hb
          simp only [LoopSlots.desc, hb, Option.isNone_none, ↓reduceIte, lsStep]
          omega
        | some len =>
          simp only [LoopSlots.desc, hb, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, lsStep]
          omega
      rw [e] at this
      exact this
    have hsteps := ls_rounds H rd chk hkeys x p m.k m.o m.pk m.kp m.bound tb st a nd kd K ci fs ad chainLimit
      ch g i s sl p' back r hk hslots i0 hcond hch hno
    show Steps _ _ _
    refine Steps.trans hsteps ?_
    simp only [lsLoop]
    iterate 3 mstep
    rw [ls_writeSlots _ _ _ _ _ _ h1 h2]
    exact .refl _


open Engine.Accel.Table in
/-- The sparse HasProperty loop's skip (`loopRow`) is the specification's steps: the rounds it skips, up to the
test of the round after them. Under the entry's Number::toString at integers (`LsIntKeys`). -/
theorem loopSkip_row [PinsHold] (hkeys : LsIntKeys) (c : Cfg F) (back : Bool) (l : Loop F)
    (t : Op) (run : Run F (Nat × List (Slot × Val F)))
    (hc : c.ctl = .loop (.spend back) l) (hit : l.it = .while_ t)
    (hrun : loopRow.loop l.p t l.body none c.top.slots c.s = some run) :
    Sim (Ctx.spec Engine.P' H rd chk) c (bindR c run fun (g, ws) c =>
      loopTest (c.mapTop fun f => { f with slots := writeSlots ws f.slots }) { l with r := l.r + g + 1 } t) := by
  have hrun' : (hasPropLoop l.p t l.body).bind (fun m => skipRun m none c.top.slots c.s) = some run := hrun
  obtain ⟨m, hm, hs⟩ := Option.bind_eq_some_iff.mp hrun'
  obtain ⟨e1, ⟨tb, e2⟩, h1, h2, h3, h4, h5, h6, h7⟩ := ls_match l.p t l.body m hm
  exact ls_sim H rd chk hkeys c back l t m tb run hc hit e1 e2 h1 h2 h3 h4 h5 h6 h7 hs


end Engine.Machine
