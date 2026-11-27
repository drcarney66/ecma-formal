module

public import Engine.Proofs.Step.Sym
public import Engine.Proofs.Step.Table
public import Engine.Proofs.Step.Rows.Contains
public import Engine.Proofs.Step.Rows.LoopSkip.Round
public import Engine.Proofs.Math
public import Engine.Proofs.Digits

@[expose] public section

/-!
# Numeric index and conversion shortcut proofs

* `toNum_algRow`: `ToNumber` on Numbers, `undefined`, `null`, and Booleans.
* `cnis_algRow`: `CanonicalNumericIndexString` on `"-0"`.
* `roundDecMV_algRow`: `@formal-rounddecimalmv(m, 0)` on non-negative safe integers `0 ≤ m < 2^53`.
* `snv_sdoRow`: `StringNumericValue` SDO on plain decimal integer `|StringNumericLiteral|` Parse Nodes `< 2^53`.
-/

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel

variable (H : Host F) (chk : Bool)

/-! ## Primitive sort tests for `ToNumber` -/

set_option maxRecDepth 8000 in
private theorem sortDef_big : Engine.P.sortDef Known.sBigInt = none := by
  rw [sortDef_eq]; rfl

private theorem tn_sort_num_true (s : State F) (fr : List (Frame F)) (x : F.Num) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sNumber (.num x))⟩ = .inl ⟨s, fr, .val (.bool true)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_1, sortTest]; rfl

private theorem tn_sort_num_undef (s : State F) (fr : List (Frame F)) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sNumber .undefined)⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_1, sortTest]; rfl

private theorem tn_sort_sym_undef (s : State F) (fr : List (Frame F)) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sSymbol .undefined)⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_4, sortTest]; rfl

private theorem tn_sort_big_undef (s : State F) (fr : List (Frame F)) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sBigInt .undefined)⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, sortDef_big, sortTest]; rfl

private theorem tn_sort_num_null (s : State F) (fr : List (Frame F)) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sNumber .null)⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_1, sortTest]; rfl

private theorem tn_sort_sym_null (s : State F) (fr : List (Frame F)) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sSymbol .null)⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_4, sortTest]; rfl

private theorem tn_sort_big_null (s : State F) (fr : List (Frame F)) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sBigInt .null)⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, sortDef_big, sortTest]; rfl

private theorem tn_sort_num_bool (s : State F) (fr : List (Frame F)) (b : Bool) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sNumber (.bool b))⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_1, sortTest]; rfl

private theorem tn_sort_sym_bool (s : State F) (fr : List (Frame F)) (b : Bool) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sSymbol (.bool b))⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_4, sortTest]; rfl

private theorem tn_sort_big_bool (s : State F) (fr : List (Frame F)) (b : Bool) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sBigInt (.bool b))⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, sortDef_big, sortTest]; rfl

/-! ## `ToNumber` -/

theorem toNum_row [PinsHold] (c : Cfg F) (vs : List (Val F))
    (r : Run F (Option (Val F))) (nd : Option F.Node) (he : toNumEntry vs = some r)
    (hstep : step (Ctx.spec Engine.P' H chk) c =
      enterAlg (Ctx.spec Engine.P' H chk) c toNumAlg nd (toNumAlg.args vs) toNumAlg.header.rc true true) :
    Sim (Ctx.spec Engine.P' H chk) c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step (Ctx.spec Engine.P' H chk) c) := by
  have hcode : (Ctx.spec Engine.P' H chk).algCode toNumAlg.id = toNumCode :=
    algCode_pin H chk _ _ toNumCode_pin
  obtain ⟨st, fs, ctl⟩ := c
  unfold toNumEntry at he
  split at he
  · rename_i x
    cases Option.some.inj he
    show Steps _ _ _
    refine Steps.next hstep ?_; rw [hcode]
    gsteps
    refine Steps.next (tn_sort_num_true H chk _ _ x) ?_
    gsteps; exact .refl _
  · cases Option.some.inj he
    show Steps _ _ _
    refine Steps.next hstep ?_; rw [hcode]
    gsteps
    refine Steps.next (tn_sort_num_undef H chk _ _) ?_
    gsteps
    refine Steps.next (tn_sort_sym_undef H chk _ _) ?_
    gsteps
    refine Steps.next (tn_sort_big_undef H chk _ _) ?_
    gsteps; exact .refl _
  · cases Option.some.inj he
    show Steps _ _ _
    refine Steps.next hstep ?_; rw [hcode]
    gsteps
    refine Steps.next (tn_sort_num_null H chk _ _) ?_
    gsteps
    refine Steps.next (tn_sort_sym_null H chk _ _) ?_
    gsteps
    refine Steps.next (tn_sort_big_null H chk _ _) ?_
    gsteps; exact .refl _
  · cases Option.some.inj he
    show Steps _ _ _
    refine Steps.next hstep ?_; rw [hcode]
    gsteps
    refine Steps.next (tn_sort_num_bool H chk _ _ false) ?_
    gsteps
    refine Steps.next (tn_sort_sym_bool H chk _ _ false) ?_
    gsteps
    refine Steps.next (tn_sort_big_bool H chk _ _ false) ?_
    gsteps; exact .refl _
  · cases Option.some.inj he
    show Steps _ _ _
    refine Steps.next hstep ?_; rw [hcode]
    gsteps
    refine Steps.next (tn_sort_num_bool H chk _ _ true) ?_
    gsteps
    refine Steps.next (tn_sort_sym_bool H chk _ _ true) ?_
    gsteps
    refine Steps.next (tn_sort_big_bool H chk _ _ true) ?_
    gsteps; exact .refl _
  · cases he

theorem toNum_algRow [PinsHold] :
    AlgRow (Ctx.spec Engine.P' H chk) ⟨Known.cToNumber, 0⟩ toNumEntry :=
  ⟨toNumAlg, toNumAlg_pin, fun c vs r nd he hstep => toNum_row H chk c vs r nd he hstep⟩

/-! ## `CanonicalNumericIndexString` on `"-0"` -/

private theorem utf16_minusZero : Model.utf16 "-0" = #[45, 48] := by
  unfold Model.utf16; rw [String.foldl_eq_foldl_toList]; rfl

theorem cnis_row [PinsHold] (c : Cfg F) (vs : List (Val F))
    (r : Run F (Option (Val F))) (nd : Option F.Node) (he : cnisEntry vs = some r)
    (hstep : step (Ctx.spec Engine.P' H chk) c =
      enterAlg (Ctx.spec Engine.P' H chk) c cnisAlg nd (cnisAlg.args vs) cnisAlg.header.rc true true) :
    Sim (Ctx.spec Engine.P' H chk) c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step (Ctx.spec Engine.P' H chk) c) := by
  unfold cnisEntry at he
  split at he
  · rename_i s
    by_cases hs : (s == #[45, 48]) = true
    · simp only [hs, ↓reduceIte, Option.some.injEq] at he
      subst he
      have hs' : s = #[45, 48] := beq_iff_eq.mp hs
      subst hs'
      obtain ⟨st, fs, ctl⟩ := c
      have hcode : (Ctx.spec Engine.P' H chk).algCode cnisAlg.id = cnisCode :=
        algCode_pin H chk _ _ cnisCode_pin
      show Steps _ _ _
      refine Steps.next hstep ?_; rw [hcode]
      gsteps
      rw [utf16_minusZero]
      gsteps
      exact .refl _
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at he; cases he
  · cases he

theorem cnis_algRow [PinsHold] :
    AlgRow (Ctx.spec Engine.P' H chk) ⟨Known.cCanonicalNumericIndexString, 0⟩ cnisEntry :=
  ⟨cnisAlg, cnisAlg_pin, fun c vs r nd he hstep => cnis_row H chk c vs r nd he hstep⟩

/-! ## `@formal-rounddecimalmv(m, 0)` on `0 ≤ m < 2^53` -/

private theorem rat_pow_nat_int (n k : Nat) : ((n : Rat) ^ k) = (((n ^ k : Nat) : Int) : Rat) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Rat.pow_succ, ih, Nat.pow_succ, Int.natCast_mul, Rat.intCast_mul]
    rfl

private theorem decExp_safe_bounds {m : Int} (hm0 : 0 < m) (hm53 : m < 2 ^ 53) :
    0 ≤ Model.Digits.decExp (m : Rat) ∧ Model.Digits.decExp (m : Rat) ≤ 15 := by
  have hmQ : (0 : Rat) < (m : Rat) := Rat.intCast_lt_intCast.2 hm0
  obtain ⟨hlo, hhi⟩ := Model.Digits.decExp_spec hmQ
  constructor
  · by_cases hge : 0 ≤ Model.Digits.decExp (m : Rat)
    · exact hge
    · exfalso
      have hp := Model.Digits.zp_le (r := 10) (by decide) (show Model.Digits.decExp (m : Rat) + 1 ≤ 0 by omega)
      simp only [Rat.zpow_zero] at hp
      have h1 : (1 : Rat) ≤ (m : Rat) := Rat.intCast_le_intCast.2 hm0
      grind
  · by_cases hle : Model.Digits.decExp (m : Rat) ≤ 15
    · exact hle
    · exfalso
      have hp := Model.Digits.zp_le (r := 10) (by decide) (show (16 : Int) ≤ Model.Digits.decExp (m : Rat) by omega)
      have hm16 : (m : Rat) < ((10 : Nat) : Rat) ^ (16 : Int) := by
        have hlt16 : m < ((10 ^ 16 : Nat) : Int) := by omega
        have hq := Rat.intCast_lt_intCast.2 hlt16
        rw [← rat_pow_nat_int 10 16, ← Rat.zpow_natCast] at hq
        exact hq
      grind

private theorem prim_decExp (m : Int) (hm0 : 0 < m) (st : State F) :
    Ecma.prim Known.pDecimalExponent [.math (Model.MathVal.int m)] st =
      .ok (.math (Model.MathVal.int (Model.Digits.decExp (m : Rat)))) st := by
  show Prims.Numbers.decimalExponent [.math (Model.MathVal.int m)] st = _
  have hlt : Model.MathVal.lt (Model.MathVal.int 0) (Model.MathVal.int m) = true := decide_eq_true hm0
  show (if Model.MathVal.lt (Model.MathVal.int 0) (Model.MathVal.int m) then
      Run.pure (Val.math (M := F) (Model.MathVal.int (Model.Digits.decExp (Model.MathVal.int m).toQ)))
    else Run.stop .sortError) st = _
  simp only [hlt, ↓reduceIte, Model.MathVal.toQ_int, Run.pure]

private theorem pow10_nat_int (k : Nat) :
    Model.MathVal.pow (.int 10) (.int k) = .int ((10 ^ k : Nat) : Int) := by
  rw [Model.MathVal.pow_nat]
  apply Model.MathVal.toQ_inj
  rw [Model.MathVal.toQ_ofQ, Model.MathVal.toQ_int, Model.MathVal.toQ_int]
  exact rat_pow_nat_int 10 k

theorem ph20_steps [PinsHold] (st : State F) (fr : List (Frame F)) (m : Int) (hm0 : 0 < m) (hm53 : m < 2 ^ 53) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, fr, .invoke (.alg ⟨Known.cPhTwentySignificantDigits, 0⟩ [.math (.int m)])⟩
      ⟨st, fr, .val (.bool true)⟩ := by
  refine Steps.next (step_alg H chk _ _ _ _ _ _ ph20DigitsAlg_pin ph20DigitsCode_pin) ?_
  obtain ⟨he0, he15⟩ := decExp_safe_bounds hm0 hm53
  let e := Model.Digits.decExp (m : Rat)
  have hsub : (19 : Int) + -e = (((19 - e.toNat : Nat) : Int)) := by omega
  have hpow : Model.MathVal.pow (.int 10) (.int (19 + -e)) = .int ((10 ^ (19 - e.toNat) : Nat) : Int) := by
    rw [hsub]; exact pow10_nat_int (19 - e.toNat)
  have hval : ((Model.MathVal.int m).mul
      (Model.MathVal.pow (mathOf.numeral (M := F) (Numeral.dec 10))
        (Model.MathVal.add (mathOf.numeral (M := F) (Numeral.dec 19))
          (Model.MathVal.int e).neg))) =
      Model.MathVal.int (m * ((10 ^ (19 - e.toNat) : Nat) : Int)) := by
    change (Model.MathVal.int m).mul ((Model.MathVal.int 10).pow (Model.MathVal.int (19 + -e))) = _
    rw [hpow]; rfl
  cases chk
  · gsteps
    refine Steps.codeIf false (by mdecide) ?_
    gsteps
    mprim (prim_decExp m hm0 _)
    gsteps
    rw [hval]
    refine Steps.next (step_sort_int H false _ _ _) ?_
    gsteps; exact .refl _
  · gsteps
    refine Steps.valBool true (by mdecide) ?_
    gsteps
    refine Steps.codeIf false (by mdecide) ?_
    gsteps
    mprim (prim_decExp m hm0 _)
    gsteps
    rw [hval]
    refine Steps.next (step_sort_int H true _ _ _) ?_
    gsteps; exact .refl _

theorem roundMVRes_steps [PinsHold] (st : State F) (fr : List (Frame F)) (m : Int) (hm0 : 0 < m) (hm53 : m < 2 ^ 53) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, fr, .invoke (.alg ⟨Known.cRoundMVResult, 0⟩ [.math (.int m)])⟩
      ⟨st, fr, .val (.num (F.numOf (.int m)))⟩ := by
  refine Steps.next (step_alg H chk _ _ _ _ _ _ roundMVResAlg_pin roundMVResCode_pin) ?_
  gsteps
  refine Steps.trans (ph20_steps H chk _ _ m hm0 hm53) ?_
  gsteps
  have hne : Model.MathVal.eq (.int m) (.int (0 : Nat)) = false := by simp [Model.MathVal.eq]; omega
  have hrc : roundMVResAlg.header.rc = false := rfl
  simp only [hrc, retConv, usedV, hne, Bool.false_eq_true, ↓reduceIte]
  exact .refl _

theorem roundDecMV_body [PinsHold] (st : State F) (fr : List (Frame F)) (a : AlgId) (nd : Option F.Node)
    (m : Int) (hm0 : 0 ≤ m) (hm53 : m < 2 ^ 53) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨a, nd, #[.math (.int m), .math (.int 0), .unbound], .steps false true true, [], [], none⟩ :: fr,
        .code roundDecMVCode⟩
      ⟨st, fr, .val (.num (numOfSafeNat m.toNat))⟩ := by
  by_cases hz : m = 0
  · subst hz
    have h0 : numOfSafeNat (0 : Int).toNat = F.numZero false := rfl
    rw [h0]
    gsteps; exact .refl _
  · have hpos : 0 < m := by omega
    have hnz : numOfSafeNat m.toNat = F.numOf (.int m) := by
      unfold numOfSafeNat
      have h1 : (m.toNat == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      have h2 : ((m.toNat : Nat) : Int) = m := Int.toNat_of_nonneg hm0
      simp only [h1, Bool.false_eq_true, ↓reduceIte, h2]
    rw [hnz]
    obtain ⟨he0, he15⟩ := decExp_safe_bounds hpos hm53
    gsteps
    refine Steps.codeIf false (by mdecide) ?_
    gsteps
    mprim (prim_decExp m hpos _)
    gsteps
    refine Steps.codeIf false (by mdecide) ?_
    gsteps
    refine Steps.codeIf false (by mdecide) ?_
    gsteps
    have hm1 : [Val.math (M := F) ((Model.MathVal.int m).mul
        (Model.MathVal.pow (mathOf.numeral (M := F) (Numeral.dec 10)) (Model.MathVal.int 0)))].reverse =
        [Val.math (M := F) (Model.MathVal.int m)] := by
      simp only [List.reverse_singleton, numeral_dec]
      change [Val.math (M := F) ((Model.MathVal.int m).mul (Model.MathVal.pow (.int 10) (.int (0 : Nat))))] = _
      rw [pow10_nat_int 0]
      show [Val.math (M := F) (Model.MathVal.int (m * 1))] = _
      rw [Int.mul_one]
    rw [hm1]
    refine Steps.trans (roundMVRes_steps H chk _ _ m hpos hm53) ?_
    gsteps; exact .refl _

theorem roundDecMV_steps [PinsHold] (st : State F) (fr : List (Frame F))
    (m : Int) (hm0 : 0 ≤ m) (hm53 : m < 2 ^ 53) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, fr, .invoke (.alg ⟨Known.cFormalRoundDecimalMV, 0⟩ [.math (.int m), .math (.int 0)])⟩
      ⟨st, fr, .val (.num (numOfSafeNat m.toNat))⟩ := by
  refine Steps.next (step_alg H chk _ _ _ _ _ _ roundDecMVAlg_pin roundDecMVCode_pin) ?_
  exact roundDecMV_body H chk st fr _ none m hm0 hm53

theorem roundDecMV_row [PinsHold] (c : Cfg F) (vs : List (Val F))
    (r : Run F (Option (Val F))) (nd : Option F.Node) (he : roundDecMVEntry vs = some r)
    (hstep : step (Ctx.spec Engine.P' H chk) c =
      enterAlg (Ctx.spec Engine.P' H chk) c roundDecMVAlg nd (roundDecMVAlg.args vs) roundDecMVAlg.header.rc true true) :
    Sim (Ctx.spec Engine.P' H chk) c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step (Ctx.spec Engine.P' H chk) c) := by
  unfold roundDecMVEntry at he
  split at he
  · rename_i m
    by_cases hm : 0 ≤ m ∧ m < 2 ^ 53
    · simp only [hm, and_self, ↓reduceIte, Option.some.injEq] at he
      subst he
      obtain ⟨st, fs, ctl⟩ := c
      have hcode : (Ctx.spec Engine.P' H chk).algCode roundDecMVAlg.id = roundDecMVCode :=
        algCode_pin H chk _ _ roundDecMVCode_pin
      show Steps _ _ _
      refine Steps.next hstep ?_; rw [hcode]
      exact roundDecMV_body H chk st fs _ nd m hm.1 hm.2
    · simp only [hm, ↓reduceIte] at he; cases he
  · cases he

theorem roundDecMV_algRow [PinsHold] :
    AlgRow (Ctx.spec Engine.P' H chk) ⟨Known.cFormalRoundDecimalMV, 0⟩ roundDecMVEntry :=
  ⟨roundDecMVAlg, roundDecMVAlg_pin, fun c vs r nd he hstep => roundDecMV_row H chk c vs r nd he hstep⟩

/-! ## `StringNumericValue` SDO on plain decimal integer `StringNumericLiteral` Parse Nodes -/

private theorem snvRowHas_spec {s : SdoId} {k : ProdId} {n : Nat} {code : Code}
    (h : snvRowHas s k n code = true) :
    ∃ r, Engine.P.row s k = some r ∧ r.vars.size = n ∧ Engine.P'.row s k = some code := by
  unfold snvRowHas at h
  split at h
  · rename_i r hr
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨r, hr, h.1, Code.optEqB_sound _ _ h.2⟩
  · cases h

private theorem snvChainHas_spec {s : SdoId} {k : ProdId} {ch : NtId}
    (h : snvChainHas s k ch = true) :
    Engine.P.row s k = none ∧ Engine.P.chain k = some ch := by
  unfold snvChainHas at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at h
  exact h

private theorem snv_enter (s : State F) (fr : List (Frame F)) (sd : SdoId) (nd : F.Node)
    (hsd : sd = Known.sdoStringNumericValue ∨ sd = Known.sdoMV) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [])⟩ =
      sdoEnter (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [])⟩ sd nd [] := by
  rcases hsd with rfl | rfl <;>
    simp [step, invoke, Known.sdoEarlyErrors, Known.sdoStringNumericValue, Known.sdoMV]

private theorem snv_at_row (s : State F) (fr : List (Frame F)) (sd : SdoId) (nd : F.Node)
    (hsd : sd = Known.sdoStringNumericValue ∨ sd = Known.sdoMV)
    (har : Engine.P.sdoArity sd = 0) (hrc0 : Engine.P.sdoRc sd = false)
    (r : Ecma.SdoRow) (sl : Array (Val F)) (code : Code) (v : Val F)
    (hrow : Engine.P.row sd (F.nodeProd nd) = some r)
    (hsl : initSlots r.vars.size (padArgs 0 []) = sl)
    (hcode : Engine.P'.row sd (F.nodeProd nd) = some code)
    (hsteps : ∀ (s' : State F) (fs' : List (Frame F)), Steps (Ctx.spec Engine.P' H chk)
      ⟨s', ⟨r.id, some nd, sl, .steps false true false, [], [], none⟩ :: fs', .code code⟩
      ⟨s', fs', .val v⟩) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [])⟩ ⟨s, fr, .val v⟩ := by
  have hrc : (Ctx.spec Engine.P' H chk).rowCode sd (F.nodeProd nd) = code := by
    show (Engine.P'.row _ _).getD _ = _; rw [hcode]; rfl
  have he : step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [])⟩ =
      .inl ⟨{ s with evalNodes := nd :: s.evalNodes },
        ⟨r.id, some nd, sl, .steps false true false, [], [], none⟩ ::
          containsPush fr (.scope (.nodes s.evalNodes (nd :: s.evalNodes))), .code code⟩ := by
    rw [snv_enter H chk s fr sd nd hsd]
    unfold sdoEnter
    simp only [spec_P, hrow, hrc, har, List.map_nil, hsl, hrc0]
    cases fr <;> rfl
  exact Steps.next he (Steps.trans (hsteps _ _) (contains_scope_ret _ _ fr _ _ _))

private theorem snv_at_chain (s : State F) (fr : List (Frame F)) (sd : SdoId) (nd : F.Node)
    (hsd : sd = Known.sdoStringNumericValue ∨ sd = Known.sdoMV)
    (hdflt : Engine.P.sdoDefault sd = none) (k : NtId) (ch : F.Node) (v : Val F)
    (hrow : Engine.P.row sd (F.nodeProd nd) = none)
    (hk : Engine.P.chain (F.nodeProd nd) = some k)
    (hch : F.nodeChild nd k 0 = some (some ch))
    (hsteps : ∀ (s' : State F) (fs' : List (Frame F)), Steps (Ctx.spec Engine.P' H chk)
      ⟨s', fs', .invoke (.sdo sd ch [])⟩ ⟨s', fs', .val v⟩) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [])⟩ ⟨s, fr, .val v⟩ := by
  have hd : (Engine.P.sdoDefault sd).bind Engine.P.alg = none := by rw [hdflt]; rfl
  have hch' : Model.nodeChild nd k 0 = some (some ch) := hch
  have he : step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [])⟩ =
      .inl ⟨{ s with evalNodes := nd :: s.evalNodes },
        containsPush fr (.scope (.nodes s.evalNodes (nd :: s.evalNodes))), .invoke (.sdo sd ch [])⟩ := by
    rw [snv_enter H chk s fr sd nd hsd]
    unfold sdoEnter
    simp only [spec_P, hrow, hd, hk, hch']
    cases fr <;> rfl
  exact Steps.next he (Steps.trans (hsteps _ _) (contains_scope_ret _ _ fr _ _ _))

private theorem childNode_spec {nd c : F.Node} {k : NtId} (h : childNode nd k = some c) :
    F.nodeChild nd k 0 = some (some c) := by
  unfold childNode at h
  split at h
  · cases Option.some.inj h; assumption
  · cases h

private theorem opt_bind_some {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

private theorem guard_bind_some {p : Prop} [Decidable p] {α : Type} {f : Unit → Option α} {v : α}
    (h : (guard p >>= f) = some v) : p ∧ f () = some v := by
  by_cases hp : p
  · have hg : (guard p : Option Unit) = some () := ite_eq_left hp
    rw [hg] at h
    exact ⟨hp, h⟩
  · have hg : (guard p : Option Unit) = none := ite_eq_right hp
    rw [hg] at h
    cases h

private theorem snv_checks [PinsHold] :
    Engine.P.sdoArity Known.sdoStringNumericValue = 0 ∧
    Engine.P.sdoRc Known.sdoStringNumericValue = false ∧
    Engine.P.sdoDefault Known.sdoStringNumericValue = none ∧
    Engine.P.sdoArity Known.sdoMV = 0 ∧
    Engine.P.sdoRc Known.sdoMV = false ∧
    Engine.P.sdoDefault Known.sdoMV = none ∧
    snvRowHas Known.sdoStringNumericValue Known.prodStrNumLit 0 snvStrNumLitCode = true ∧
    snvChainHas Known.sdoStringNumericValue Known.prodStrNumDec Known.ntStrDecimalLiteral = true ∧
    snvChainHas Known.sdoStringNumericValue Known.prodStrDecUnsigned Known.ntStrUnsignedDecimalLiteral = true ∧
    snvRowHas Known.sdoStringNumericValue Known.prodStrUnsignedDigits 2 snvStrUnsignedDigitsCode = true ∧
    snvChainHas Known.sdoMV Known.prodDecDigits1 Known.ntDecimalDigit = true ∧
    snvRowHas Known.sdoMV Known.prodDecDigitsStep 0 mvDecDigitsStepCode = true ∧
    (decDigitProds.all fun (p, d) => snvRowHas Known.sdoMV p 0 (mvDecDigitCode d)) = true := by
  have h := snvRows_true
  simp only [snvRowsCheck, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isNone_iff_eq_none, and_assoc] at h
  exact h

private theorem decDigitVal_mem {nd : F.Node} {d : Nat} (h : decDigitVal nd = some d) :
    (F.nodeProd nd, d) ∈ decDigitProds := by
  change (if (F.nodeProd nd == Known.prodDecDigit0) = true then some 0
    else if (F.nodeProd nd == Known.prodDecDigit1) = true then some 1
    else if (F.nodeProd nd == Known.prodDecDigit2) = true then some 2
    else if (F.nodeProd nd == Known.prodDecDigit3) = true then some 3
    else if (F.nodeProd nd == Known.prodDecDigit4) = true then some 4
    else if (F.nodeProd nd == Known.prodDecDigit5) = true then some 5
    else if (F.nodeProd nd == Known.prodDecDigit6) = true then some 6
    else if (F.nodeProd nd == Known.prodDecDigit7) = true then some 7
    else if (F.nodeProd nd == Known.prodDecDigit8) = true then some 8
    else if (F.nodeProd nd == Known.prodDecDigit9) = true then some 9
    else none) = some d at h
  split at h; · rename_i hp; cases Option.some.inj h; rw [beq_iff_eq.mp hp]; simp [decDigitProds]
  split at h; · rename_i hp; cases Option.some.inj h; rw [beq_iff_eq.mp hp]; simp [decDigitProds]
  split at h; · rename_i hp; cases Option.some.inj h; rw [beq_iff_eq.mp hp]; simp [decDigitProds]
  split at h; · rename_i hp; cases Option.some.inj h; rw [beq_iff_eq.mp hp]; simp [decDigitProds]
  split at h; · rename_i hp; cases Option.some.inj h; rw [beq_iff_eq.mp hp]; simp [decDigitProds]
  split at h; · rename_i hp; cases Option.some.inj h; rw [beq_iff_eq.mp hp]; simp [decDigitProds]
  split at h; · rename_i hp; cases Option.some.inj h; rw [beq_iff_eq.mp hp]; simp [decDigitProds]
  split at h; · rename_i hp; cases Option.some.inj h; rw [beq_iff_eq.mp hp]; simp [decDigitProds]
  split at h; · rename_i hp; cases Option.some.inj h; rw [beq_iff_eq.mp hp]; simp [decDigitProds]
  split at h; · rename_i hp; cases Option.some.inj h; rw [beq_iff_eq.mp hp]; simp [decDigitProds]
  cases h

theorem mv_digit_steps [PinsHold] (nd : F.Node) (d : Nat) (h : decDigitVal nd = some d)
    (s : State F) (fr : List (Frame F)) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, fr, .invoke (.sdo Known.sdoMV nd [])⟩
      ⟨s, fr, .val (.math (.int d))⟩ := by
  obtain ⟨_, _, _, har, hrc, _, _, _, _, _, _, _, hall⟩ := snv_checks
  have hmem := decDigitVal_mem h
  have hhas : snvRowHas Known.sdoMV (F.nodeProd nd) 0 (mvDecDigitCode d) = true :=
    List.all_eq_true.mp hall (F.nodeProd nd, d) hmem
  obtain ⟨r, hrow, hn, hcode⟩ := snvRowHas_spec hhas
  refine snv_at_row H chk s fr Known.sdoMV nd (.inr rfl) har hrc r #[] (mvDecDigitCode d) (.math (.int d)) hrow
    (by rw [hn]; rfl) hcode fun s' fs' => ?_
  unfold mvDecDigitCode
  csteps; exact .refl _

theorem mv_digits_steps [PinsHold] :
    ∀ (fuel : Nat) (nd : F.Node) (v : Nat),
      decDigitsVal fuel nd = some v →
      ∀ (s : State F) (fr : List (Frame F)),
        Steps (Ctx.spec Engine.P' H chk)
          ⟨s, fr, .invoke (.sdo Known.sdoMV nd [])⟩
          ⟨s, fr, .val (.math (.int v))⟩ := by
  intro fuel
  induction fuel with
  | zero => intro nd v h; simp [decDigitsVal] at h
  | succ fuel ih =>
    intro nd v h s fr
    obtain ⟨_, _, _, har, hrc, hdflt, _, _, _, _, hch1, hstepR, _⟩ := snv_checks
    change (if (F.nodeProd nd == Known.prodDecDigits1) = true then
        childNode nd Known.ntDecimalDigit >>= decDigitVal
      else if (F.nodeProd nd == Known.prodDecDigitsStep) = true then do
        let pre ← childNode nd Known.ntDecimalDigits
        let d ← childNode nd Known.ntDecimalDigit
        let v ← decDigitsVal fuel pre
        let dv ← decDigitVal d
        pure (v * 10 + dv)
      else none) = some v at h
    split at h
    · rename_i hp1
      obtain ⟨dNode, hdNode, hdv⟩ := opt_bind_some h
      have hp1' : F.nodeProd nd = Known.prodDecDigits1 := beq_iff_eq.mp hp1
      obtain ⟨hrow, hch⟩ := snvChainHas_spec hch1
      refine snv_at_chain H chk s fr Known.sdoMV nd (.inr rfl) hdflt Known.ntDecimalDigit dNode (.math (.int v))
        (hp1' ▸ hrow) (hp1' ▸ hch) (childNode_spec hdNode) fun s' fs' =>
        mv_digit_steps H chk dNode v hdv s' fs'
    · split at h
      · rename_i hp2
        obtain ⟨pre, hpre, h⟩ := opt_bind_some h
        obtain ⟨dNode, hdNode, h⟩ := opt_bind_some h
        obtain ⟨vp, hvp, h⟩ := opt_bind_some h
        obtain ⟨dv, hdv, h⟩ := opt_bind_some h
        cases Option.some.inj h
        have hp2' : F.nodeProd nd = Known.prodDecDigitsStep := beq_iff_eq.mp hp2
        obtain ⟨r, hrow, hn, hcode⟩ := snvRowHas_spec hstepR
        refine snv_at_row H chk s fr Known.sdoMV nd (.inr rfl) har hrc r #[] mvDecDigitsStepCode
          (.math (.int ((vp * 10 + dv : Nat) : Int))) (hp2' ▸ hrow) (by rw [hn]; rfl) (hp2' ▸ hcode) fun s' fs' => ?_
        unfold mvDecDigitsStepCode
        csteps
        refine Steps.next (contains_child_some _ _ _ _ _ _ _ _ _ _ _ _ (childNode_spec hpre)) ?_
        csteps
        refine Steps.trans (ih pre vp hvp _ _) ?_
        csteps
        refine Steps.next (contains_child_some _ _ _ _ _ _ _ _ _ _ _ _ (childNode_spec hdNode)) ?_
        csteps
        refine Steps.trans (mv_digit_steps H chk dNode dv hdv _ _) ?_
        csteps
        have hmath : ((vp : Int) * 10 + (dv : Int)) = ((vp * 10 + dv : Nat) : Int) := by omega
        show Steps _ ⟨s', fs', .val (.math (.int ((vp : Int) * 10 + (dv : Int))))⟩ _
        rw [hmath]
        exact .refl _
      · cases h

private theorem snvPlainNat_spec {nd : F.Node} {v : Nat} (h : snvPlainNat nd = some v) :
    ∃ n1 n2 n3 ds,
      F.nodeProd nd = Known.prodStrNumLit ∧
      F.nodeChild nd Known.ntStrNumericLiteral 0 = some (some n1) ∧
      F.nodeProd n1 = Known.prodStrNumDec ∧
      F.nodeChild n1 Known.ntStrDecimalLiteral 0 = some (some n2) ∧
      F.nodeProd n2 = Known.prodStrDecUnsigned ∧
      F.nodeChild n2 Known.ntStrUnsignedDecimalLiteral 0 = some (some n3) ∧
      F.nodeProd n3 = Known.prodStrUnsignedDigits ∧
      F.nodeChild n3 Known.ntDecimalDigits 0 = some (some ds) ∧
      F.nodeChild n3 Known.ntExponentPart 0 = some none ∧
      decDigitsVal 16 ds = some v ∧
      v < 2 ^ 53 := by
  unfold snvPlainNat at h
  obtain ⟨hp0, h⟩ := guard_bind_some h
  obtain ⟨n1, hn1, h⟩ := opt_bind_some h
  obtain ⟨hp1, h⟩ := guard_bind_some h
  obtain ⟨n2, hn2, h⟩ := opt_bind_some h
  obtain ⟨hp2, h⟩ := guard_bind_some h
  obtain ⟨n3, hn3, h⟩ := opt_bind_some h
  obtain ⟨hp3, h⟩ := guard_bind_some h
  obtain ⟨ds, hds, h⟩ := opt_bind_some h
  obtain ⟨hexp, h⟩ := guard_bind_some h
  obtain ⟨v', hv', h⟩ := opt_bind_some h
  obtain ⟨hv53, h⟩ := guard_bind_some h
  cases Option.some.inj h
  exact ⟨n1, n2, n3, ds,
    beq_iff_eq.mp hp0, childNode_spec hn1,
    beq_iff_eq.mp hp1, childNode_spec hn2,
    beq_iff_eq.mp hp2, childNode_spec hn3,
    beq_iff_eq.mp hp3, childNode_spec hds,
    beq_iff_eq.mp hexp, hv', hv53⟩

theorem snv_plain_steps [PinsHold] (nd : F.Node) (v : Nat) (h : snvPlainNat nd = some v)
    (s : State F) (fr : List (Frame F)) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, fr, .invoke (.sdo Known.sdoStringNumericValue nd [])⟩
      ⟨s, fr, .val (.num (numOfSafeNat v))⟩ := by
  obtain ⟨har, hrc, hdflt, _, _, _, hlit, hch1, hch2, hud, _, _, _⟩ := snv_checks
  obtain ⟨n1, n2, n3, ds, hp0', hn1, hp1', hn2, hp2', hn3, hp3', hds, hexp', hv', hv53⟩ := snvPlainNat_spec h
  obtain ⟨r0, hrow0, hn0, hcode0⟩ := snvRowHas_spec hlit
  obtain ⟨hrow1, hchain1⟩ := snvChainHas_spec hch1
  obtain ⟨hrow2, hchain2⟩ := snvChainHas_spec hch2
  obtain ⟨r3, hrow3, hn3_sz, hcode3⟩ := snvRowHas_spec hud
  refine snv_at_row H chk s fr Known.sdoStringNumericValue nd (.inl rfl) har hrc r0 #[] snvStrNumLitCode
    (.num (numOfSafeNat v)) (hp0' ▸ hrow0) (by rw [hn0]; rfl) (hp0' ▸ hcode0) fun s1 fs1 => ?_
  unfold snvStrNumLitCode
  csteps
  refine Steps.next (contains_child_some _ _ _ _ _ _ _ _ _ _ _ _ hn1) ?_
  csteps
  refine Steps.trans (snv_at_chain H chk _ _ Known.sdoStringNumericValue n1 (.inl rfl) hdflt Known.ntStrDecimalLiteral n2
    (.num (numOfSafeNat v)) (hp1' ▸ hrow1) (hp1' ▸ hchain1) hn2 fun s2 fs2 => ?_) ?_
  · refine snv_at_chain H chk s2 fs2 Known.sdoStringNumericValue n2 (.inl rfl) hdflt Known.ntStrUnsignedDecimalLiteral n3
      (.num (numOfSafeNat v)) (hp2' ▸ hrow2) (hp2' ▸ hchain2) hn3 fun s3 fs3 => ?_
    refine snv_at_row H chk s3 fs3 Known.sdoStringNumericValue n3 (.inl rfl) har hrc r3 #[.unbound, .unbound]
      snvStrUnsignedDigitsCode (.num (numOfSafeNat v)) (hp3' ▸ hrow3) (by rw [hn3_sz]; rfl) (hp3' ▸ hcode3)
      fun s4 fs4 => ?_
    unfold snvStrUnsignedDigitsCode
    csteps
    refine Steps.next (contains_child_some _ _ _ _ _ _ _ _ _ _ _ _ hds) ?_
    csteps
    refine Steps.trans (mv_digits_steps H chk 16 ds v hv' _ _) ?_
    csteps
    refine Steps.next (contains_child_none _ _ _ _ _ _ _ _ _ _ _ fun ch h => by rw [hexp'] at h; cases h) ?_
    csteps
    have hm0 : (0 : Int) ≤ (v : Int) := Int.natCast_nonneg v
    have hm53 : (v : Int) < 2 ^ 53 := by omega
    have htoNat : ((v : Int)).toNat = v := Int.toNat_natCast v
    refine Steps.trans (htoNat ▸ roundDecMV_steps H chk _ _ (v : Int) hm0 hm53) ?_
    csteps; exact .refl _
  · csteps; exact .refl _

theorem snv_sdoRow [PinsHold] :
    SdoRowOk (Ctx.spec Engine.P' H chk) Known.sdoStringNumericValue snvSdo := by
  intro c nd vs r hc he
  unfold snvSdo at he
  split at he
  · rw [Option.map_eq_some_iff] at he
    obtain ⟨v, hv, rfl⟩ := he
    obtain ⟨s, fr, ctl⟩ := c
    cases hc
    exact snv_plain_steps H chk nd v hv s fr
  · cases he

end Engine.Machine
