module

public import Engine.Proofs.Step.Sym
public import Engine.Proofs.Step.Table
public import Engine.Proofs.Step.Rows.CodePoints

@[expose] public section

/-!
# GetStringIndex's row

The engine's shortcut at GetStringIndex (`Engine.Accel.gsiEntry`: one scan of the String's code units, a
CodePointAt Record allocated for each code point before the index's) is the specification's steps: the loop of
GetStringIndex, each round a call of CodePointAt (`cpa_steps`, `Rows/CodePoints.lean`). The row holds at every String and integer: no hypothesis is added.
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-- GetStringIndex's loop's body. -/
abbrev gsiBody : Code :=
  [Ins.site [1, 5], Ins.br (Op.leaf (Leaf.rel RelOp.eq) [Op.var 4, Op.var 1]) [Ins.ret (Op.var 3)] [],
    Ins.site [2, 5], Ins.let_ 5 (Op.call (CallK.alg { clause := Known.cCodePointAt, idx := 0 }) [Op.var 0, Op.var 3]),
    Ins.site [3, 5], Ins.let_ 3 (Op.leaf (Leaf.bin BinOp.add) [Op.var 3, Op.leaf (Leaf.field Known.fCodeUnitCount) [Op.var 5]]),
    Ins.site [4, 5],
    Ins.let_ 4 (Op.leaf (Leaf.bin BinOp.add) [Op.var 4, Op.const (Const.math Sign.none (Mag.num (Numeral.dec 1)))])]

/-- GetStringIndex's loop's iterator. -/
abbrev gsiIter : Iter :=
  Iter.while_ (Op.leaf (Leaf.rel RelOp.lt) [Op.var 3, Op.var 2])

open Engine.Accel in
/-- GetStringIndex's loop and return, from a round's head: `scanIdx`'s index, its Records allocated. -/
theorem gsi_loop [PinsHold] (H : Host F) (chk : Bool) (st : State F) (fs : List (Frame F))
    (nd : Option F.Node) (s : Array UInt16) (i : Int) :
    ∀ (k p c : Nat) (rs : Array (Cell F)) (v5 : Val F) (q : List Nat) (r : Nat), p ≤ s.size → s.size - p ≤ k →
    Steps (Ctx.spec Engine.P' H chk)
      ⟨{ st with heap := st.heap ++ rs },
        ⟨⟨Known.cGetStringIndex, 0⟩, nd, #[.str s, .math (.int i), .math (.int s.size), .math (.int p), .math (.int c), v5],
          .steps false true true, q, [.seq [.site [6], .ret (.var 2)]], none⟩ :: fs,
        .loop .round ⟨none, gsiIter, [5], gsiBody, .plain, r⟩⟩
      ⟨{ st with heap := st.heap ++ (scanIdx s i k p c rs).2 }, fs, .val (.math (.int (scanIdx s i k p c rs).1))⟩ := by
  intro k
  induction k with
  | zero =>
    intro p c rs v5 q r hp hk
    gsteps
    refine Steps.valBool false (by mdecide) ?_
    gsteps
    exact .refl _
  | succ k ih =>
    intro p c rs v5 q r hp hk
    gsteps
    by_cases hlt : p < s.size
    · refine Steps.valBool true (by mdecide) ?_
      gsteps
      by_cases hc : (c : Int) = i
      · have e : scanIdx s i (k + 1) p c rs = (p, rs) := by
          rw [scanIdx, if_pos hlt, if_pos hc]
        rw [e]
        refine Steps.codeIf true (by mdecide) ?_
        gsteps
        exact .refl _
      · have e : scanIdx s i (k + 1) p c rs =
            scanIdx s i k (p + (cpAt s p).2.1) (c + 1) (rs.push (cpRec (cpAt s p))) := by
          rw [scanIdx, if_pos hlt, if_neg hc]
        rw [e]
        refine Steps.codeIf false (by mdecide) ?_
        gsteps
        refine Steps.trans (cpa_steps H chk _ _ s p hlt) ?_
        gsteps
        refine Steps.next (step_field _ _ _ _ _ _ _ _ _ _ _ _ _ (cpRec_count _ _ (cpAt s p) (heap_push_get _ _))) ?_
        rw [show (st.heap ++ rs).push (cpRec (cpAt s p)) = st.heap ++ rs.push (cpRec (cpAt s p)) from by simp]
        gsteps_round
        obtain ⟨h1, h2⟩ := cpAt_count s p hlt
        exact ih (p + (cpAt s p).2.1) (c + 1) (rs.push (cpRec (cpAt s p))) _ _ _ (by omega) (by omega)
    · have e : scanIdx s i (k + 1) p c rs = (s.size, rs) := by simp [scanIdx, hlt]
      rw [e]
      refine Steps.valBool false (by mdecide) ?_
      gsteps
      exact .refl _

open Engine.Accel in
/-- GetStringIndex's steps at a String that is not empty and an integer: `scanIdx`'s index, its Records allocated. -/
theorem gsi_steps [PinsHold] (H : Host F) (chk : Bool) (st : State F) (fs : List (Frame F))
    (nd : Option F.Node) (s : Array UInt16) (i : Int) (hs : s.size ≠ 0) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨⟨Known.cGetStringIndex, 0⟩, nd, #[.str s, .math (.int i), .unbound, .unbound, .unbound, .unbound], .steps false true true,
        [], [], none⟩ :: fs, .code gsiCode⟩
      ⟨{ st with heap := st.heap ++ (scanIdx s i s.size 0 0 #[]).2 }, fs,
        .val (.math (.int (scanIdx s i s.size 0 0 #[]).1))⟩ := by
  gsteps
  have hne : s ≠ #[] := fun h => hs (by rw [h]; rfl)
  refine Steps.valBool false (by simp [sameIs, Val.same, Val.used, utf16_empty, hne]) ?_
  gsteps_round
  have h := gsi_loop H chk st fs nd s i s.size 0 0 #[] .unbound [5] (0 + 1) (Nat.zero_le _) (by omega)
  rw [Array.append_empty] at h
  exact h

/-- GetStringIndex's steps at the empty String: 0, in the same state. -/
theorem gsi_steps_empty (H : Host F) (chk : Bool) (st : State F) (fs : List (Frame F))
    (nd : Option F.Node) (i : Int) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨⟨Known.cGetStringIndex, 0⟩, nd, #[.str #[], .math (.int i), .unbound, .unbound, .unbound, .unbound], .steps false true true,
        [], [], none⟩ :: fs, .code gsiCode⟩
      ⟨st, fs, .val (.math (.int 0))⟩ := by
  gsteps
  refine Steps.valBool true (by simp [sameIs, Val.same, Val.used, utf16_empty]) ?_
  gsteps
  exact .refl _

open Engine.Accel in
/-- The engine's shortcut at GetStringIndex is the specification's steps, from a configuration whose transition
enters the algorithm's frame. -/
theorem gsi_row [PinsHold] (H : Host F) (chk : Bool) (c : Cfg F) (vs : List (Val F))
    (r : Run F (Option (Val F))) (nd : Option F.Node) (he : gsiEntry vs = some r)
    (hstep : step (Ctx.spec Engine.P' H chk) c =
      enterAlg (Ctx.spec Engine.P' H chk) c gsiAlg nd (gsiAlg.args vs) gsiAlg.header.rc true true) :
    Sim (Ctx.spec Engine.P' H chk) c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step (Ctx.spec Engine.P' H chk) c) := by
  unfold gsiEntry at he
  split at he
  · rename_i s i
    split at he
    · cases he
      obtain ⟨st, fs, ctl⟩ := c
      have hcode : (Ctx.spec Engine.P' H chk).algCode gsiAlg.id = gsiCode := by
        show (Engine.P'.alg ⟨Known.cGetStringIndex, 0⟩).getD _ = _
        rw [gsiCode_pin]; rfl
      by_cases hs : s.size = 0
      · have hr : gsiRun s i st = .ok (.math (.int 0)) st := by unfold gsiRun; exact if_pos hs
        have hs' : s = #[] := Array.eq_empty_of_size_eq_zero hs
        subst hs'
        simp only [bindR, always, hr, Run.Res.bind]
        show Steps _ _ _
        refine Steps.next hstep ?_
        rw [hcode]
        exact gsi_steps_empty H chk st fs nd i
      · have hr : gsiRun s i st = .ok (.math (.int (scanIdx s i s.size 0 0 #[]).1))
            { st with heap := st.heap ++ (scanIdx s i s.size 0 0 #[]).2 } := by
          unfold gsiRun; exact if_neg hs
        simp only [bindR, always, hr, Run.Res.bind]
        show Steps _ _ _
        refine Steps.next hstep ?_
        rw [hcode]
        exact gsi_steps H chk st fs nd s i hs
    · cases he
  · cases he

open Engine.Accel in
/-- GetStringIndex's row. -/
theorem gsi_algRow [PinsHold] (H : Host F) (chk : Bool) :
    AlgRow (Ctx.spec Engine.P' H chk) ⟨Known.cGetStringIndex, 0⟩ gsiEntry :=
  ⟨gsiAlg, gsiAlg_pin, fun c vs r nd he hstep => gsi_row H chk c vs r nd he hstep⟩


end Engine.Machine
