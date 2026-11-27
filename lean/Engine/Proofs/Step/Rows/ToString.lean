module

public import Engine.Proofs.Step.Sym
public import Engine.Proofs.Step.Table
public import Engine.Proofs.Step.Rows.LoopSkip.Round
public import Engine.Proofs.Step.Rows.LoopSkip.IntKeys

@[expose] public section

/-!
# The rows of `Number::toString` and `ToString`

`numToStr_algRow` and `toStr_algRow`: the engine's exact shortcuts for `Number::toString(x, 10)` on canonical
non-negative safe integers `< 2^53` and `ToString(argument)` on Strings and canonical non-negative safe integer
Numbers `< 2^53`.
-/

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel

private theorem numEq_of_beq {a b : F.Num} (h : (a == b) = true) : a = b :=
  Subtype.ext (beq_iff_eq.mp h)

theorem safeNatOf?_spec {x : F.Num} {n : Nat} (h : safeNatOf? x = some n) :
    (n = 0 ∧ x = F.numZero false) ∨ (0 < n ∧ n < 2 ^ 53 ∧ x = F.numOf (.int n)) := by
  unfold safeNatOf? at h
  by_cases hz : (x == F.numZero false) = true
  · simp only [hz, ↓reduceIte, Option.some.injEq] at h
    exact .inl ⟨h.symm, numEq_of_beq hz⟩
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
    split at h <;> try cases h
    rename_i i _
    by_cases hi : (0 < i && i < 2 ^ 53) = true
    · simp only [hi, ↓reduceIte] at h
      by_cases hx : (x == F.numOf (.int i.toNat)) = true
      · simp only [hx, ↓reduceIte, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
        exact .inr ⟨by omega, by omega, numEq_of_beq hx⟩
      · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h; cases h
    · simp only [hi, Bool.false_eq_true, ↓reduceIte] at h; cases h

set_option maxRecDepth 8000 in
theorem numToStr_steps [PinsHold] (H : Host F) (chk : Bool) (st : State F) (fs : List (Frame F))
    (a : AlgId) (nd : Option F.Node) (x : F.Num) (n : Nat) (h : safeNatOf? x = some n) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨a, nd, tsSlots x (F.ofNat 10), .steps false true true, [], [], none⟩ :: fs, .code toStringCode⟩
      ⟨st, fs, .val (.str (F.strLit (natDecStr n)))⟩ := by
  rcases safeNatOf?_spec h with ⟨rfl, rfl⟩ | ⟨hn0, hn53, rfl⟩
  · exact numIdx_zero H chk (F.ofNat 10) st fs a nd
  · have hne : (n == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp only [natDecStr, hne, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨n0, k0, s0, hv, hlt, h5, hn21, hkn, hkd, hcat⟩ := lsIntKeys.exec n hn0 hn53
    have hm0 : F.lt (F.ofNat 0) (.int n) = true := decide_eq_true (by omega)
    exact numIdx_step H chk (F.numOf (.int n)) (.int n) hv hlt hm0 n0 k0 s0 h5 hn21 hkn
      (F.strLit (toString n)) hkd hcat st fs a nd

theorem numToStr_row (H : Host F) (chk : Bool) [PinsHold] (c : Cfg F) (vs : List (Val F))
    (r : Run F (Option (Val F))) (nd : Option F.Node) (he : numToStrEntry vs = some r)
    (hstep : step (Ctx.spec Engine.P' H chk) c =
      enterAlg (Ctx.spec Engine.P' H chk) c toStringAlg nd (toStringAlg.args vs) toStringAlg.header.rc true true) :
    Sim (Ctx.spec Engine.P' H chk) c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step (Ctx.spec Engine.P' H chk) c) := by
  unfold numToStrEntry at he
  split at he
  · rename_i x
    rw [Option.map_eq_some_iff] at he
    obtain ⟨n, hn, rfl⟩ := he
    obtain ⟨st, fs, ctl⟩ := c
    have hcode : (Ctx.spec Engine.P' H chk).algCode toStringAlg.id = toStringCode := by
      show (Engine.P'.alg ⟨Known.cNumberToString, 0⟩).getD _ = _
      rw [toStringCode_pin]; rfl
    show Steps _ _ _
    refine Steps.next hstep ?_
    rw [hcode]
    exact numToStr_steps H chk st fs toStringAlg.id nd x n hn
  · cases he

theorem numToStr_algRow (H : Host F) (chk : Bool) [PinsHold] :
    AlgRow (Ctx.spec Engine.P' H chk) ⟨Known.cNumberToString, 0⟩ numToStrEntry :=
  ⟨toStringAlg, toStringAlg_pin, fun c vs r nd he hstep => numToStr_row H chk c vs r nd he hstep⟩

theorem ls_sort2_str (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F)) (t : F.Str) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sString (.str t))⟩ = .inl ⟨s, fr, .val (.bool true)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_2, sortTest]
  rfl

set_option maxRecDepth 8000 in
theorem toStr_str_steps (H : Host F) (chk : Bool) (st : State F) (fs : List (Frame F))
    (a : AlgId) (nd : Option F.Node) (t : F.Str) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨a, nd, #[.str t, .unbound], .steps true true true, [], [], none⟩ :: fs, .code lsToStringCode⟩
      ⟨st, fs, .val (.comp Known.eNormal (.str t) (.enum Known.eEmpty))⟩ := by
  gsteps
  refine Steps.next (ls_sort2_str H chk _ _ _) ?_
  gsteps
  exact .refl _

set_option maxRecDepth 8000 in
theorem toStr_num_steps [PinsHold] (H : Host F) (chk : Bool) (st : State F) (fs : List (Frame F))
    (a : AlgId) (nd : Option F.Node) (x : F.Num) (n : Nat) (h : safeNatOf? x = some n) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨a, nd, #[.num x, .unbound], .steps true true true, [], [], none⟩ :: fs, .code lsToStringCode⟩
      ⟨st, fs, .val (.comp Known.eNormal (.str (F.strLit (natDecStr n))) (.enum Known.eEmpty))⟩ := by
  gsteps
  refine Steps.next (ls_sort2 H chk _ _ _) ?_
  gsteps
  refine Steps.next (ls_sort4 H chk _ _ _) ?_
  gsteps
  refine Steps.next (ls_sort1 H chk _ _ _) ?_
  gsteps
  refine Steps.next (step_alg H chk _ _ _ _ _ _ toStringAlg_pin toStringCode_pin) ?_
  refine Steps.trans (numToStr_steps H chk st _ toStringAlg.id none x n h) ?_
  gsteps
  exact .refl _

theorem toStr_row (H : Host F) (chk : Bool) [PinsHold] (c : Cfg F) (vs : List (Val F))
    (r : Run F (Option (Val F))) (nd : Option F.Node) (he : toStrEntry vs = some r)
    (hstep : step (Ctx.spec Engine.P' H chk) c =
      enterAlg (Ctx.spec Engine.P' H chk) c lsToStringAlg nd (lsToStringAlg.args vs) lsToStringAlg.header.rc true true) :
    Sim (Ctx.spec Engine.P' H chk) c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step (Ctx.spec Engine.P' H chk) c) := by
  have hcode : (Ctx.spec Engine.P' H chk).algCode lsToStringAlg.id = lsToStringCode := by
    show (Engine.P'.alg ⟨Known.cToString, 0⟩).getD _ = _
    rw [lsToStringCode_pin]; rfl
  unfold toStrEntry at he
  split at he
  · rename_i t
    cases Option.some.inj he
    obtain ⟨st, fs, ctl⟩ := c
    show Steps _ _ _
    refine Steps.next hstep ?_
    rw [hcode]
    exact toStr_str_steps H chk st fs lsToStringAlg.id nd t
  · rename_i x
    rw [Option.map_eq_some_iff] at he
    obtain ⟨n, hn, rfl⟩ := he
    obtain ⟨st, fs, ctl⟩ := c
    show Steps _ _ _
    refine Steps.next hstep ?_
    rw [hcode]
    exact toStr_num_steps H chk st fs lsToStringAlg.id nd x n hn
  · cases he

theorem toStr_algRow (H : Host F) (chk : Bool) [PinsHold] :
    AlgRow (Ctx.spec Engine.P' H chk) ⟨Known.cToString, 0⟩ toStrEntry :=
  ⟨lsToStringAlg, lsToStringAlg_pin, fun c vs r nd he hstep => toStr_row H chk c vs r nd he hstep⟩

end Engine.Machine
