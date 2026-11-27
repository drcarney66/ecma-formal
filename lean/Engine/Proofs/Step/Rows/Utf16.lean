module

public import Engine.Proofs.Step.Sym
public import Engine.Proofs.Step.Table
public import Engine.Proofs.Step.Rows.CodePoints
public import Engine.Proofs.Math

@[expose] public section

/-!
# The rows of `UTF16EncodeCodePoint` and `CodePointsToString`

`utf16Enc_algRow` and `cpts_algRow`: exact shortcuts for `UTF16EncodeCodePoint` on valid Unicode code points
`0 ≤ cp ≤ 0x10FFFF` and `CodePointsToString` on List cells of valid Unicode code points up to `scanLimit`.
-/

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel

variable (H : Host F) (chk : Bool)

private theorem prim_unitOf (u : Int) (h0 : 0 ≤ u) (h1 : u ≤ 0xFFFF) (st : State F) :
    Ecma.prim Known.pUnitOrPointOf [.choice 1, .math (Model.MathVal.int u)] st =
      .ok (.math (Model.MathVal.int u)) st := by
  show Prims.Strings.unitOrPointOf [.choice 1, .math (Model.MathVal.int u)] st = _
  have hu : Prims.Strings.isUnit (M := F) (Model.MathVal.int u) = true := by
    simp [Prims.Strings.isUnit, Prims.Strings.inRange, Model.MathVal.lt, Model.MathVal.isInt]
    omega
  simp [Prims.Strings.unitOrPointOf, hu, Run.pure]

private theorem prim_strOf1 (u : Int) (h0 : 0 ≤ u) (h1 : u ≤ 0xFFFF) (st : State F) :
    Ecma.prim Known.pStrOfUnits [.math (Model.MathVal.int u)] st =
      .ok (.str #[UInt16.ofNat u.toNat]) st := by
  show Prims.Strings.strOfUnits [.math (Model.MathVal.int u)] st = _
  have hu : Prims.Strings.isUnit (M := F) (Model.MathVal.int u) = true := by
    simp [Prims.Strings.isUnit, Prims.Strings.inRange, Model.MathVal.lt, Model.MathVal.isInt]
    omega
  simp [Prims.Strings.strOfUnits, hu, Run.pure, utf16_empty, Model.MathVal.idx, h0, Nat.toUInt16]

private theorem prim_concat_units (u1 u2 : Int) (h1a : 0 ≤ u1) (h1b : u1 ≤ 0xFFFF)
    (h2a : 0 ≤ u2) (h2b : u2 ≤ 0xFFFF) (st : State F) :
    Ecma.prim Known.pConcat [.math (Model.MathVal.int u1), .math (Model.MathVal.int u2)] st =
      .ok (.str #[UInt16.ofNat u1.toNat, UInt16.ofNat u2.toNat]) st := by
  show Prims.Strings.strOfUnits [.math (Model.MathVal.int u1), .math (Model.MathVal.int u2)] st = _
  have hu1 : Prims.Strings.isUnit (M := F) (Model.MathVal.int u1) = true := by
    simp [Prims.Strings.isUnit, Prims.Strings.inRange, Model.MathVal.lt, Model.MathVal.isInt]; omega
  have hu2 : Prims.Strings.isUnit (M := F) (Model.MathVal.int u2) = true := by
    simp [Prims.Strings.isUnit, Prims.Strings.inRange, Model.MathVal.lt, Model.MathVal.isInt]; omega
  simp [Prims.Strings.strOfUnits, hu1, hu2, Run.pure, utf16_empty, Model.MathVal.idx, h1a, h2a, Nat.toUInt16]

private theorem relOp_le_int (a b : Int) (hab : a ≤ b) (st : State F) :
    relOp .le (Val.math (M := F) (Model.MathVal.int a)) (.math (Model.MathVal.int b)) st = .ok true st := by
  have hor : (Model.MathVal.lt (.int a) (.int b) || Model.MathVal.eq (.int a) (.int b)) = true := by
    simp [Model.MathVal.lt, Model.MathVal.eq]; omega
  show (do return (← relOp.lt (Val.math (M := F) (.int a)) (.math (.int b))) ||
      (← relOp.eq (Val.math (M := F) (.int a)) (.math (.int b)))) st = _
  simp [relOp.lt, relOp.eq, bind, Run.bind, Run.Res.bind, Pure.pure, Run.pure, hor]

private theorem prim_chain_cp (cp : Int) (h0 : 0 ≤ cp) (h1 : cp ≤ 0x10FFFF) (st : State F) :
    Ecma.prim Known.pChain
      [.math (Model.MathVal.int 0), .choice 1, .math (Model.MathVal.int cp), .choice 1,
       .math (Model.MathVal.int 0x10FFFF)] st = .ok (.bool true) st := by
  show Prims.Numbers.chain
    [.math (Model.MathVal.int 0), .choice 1, .math (Model.MathVal.int cp), .choice 1,
     .math (Model.MathVal.int 0x10FFFF)] st = _
  have hl1 := relOp_le_int 0 cp h0 st
  have hl2 := relOp_le_int cp 0x10FFFF h1 st
  simp [Prims.Numbers.chain, Prims.Numbers.chainRel, bind, Run.bind, Run.Res.bind, Pure.pure, Run.pure, hl1, hl2]

private theorem floor_mathVal (x : Model.MathVal) : Model.MathVal.floor x = .int x.toQ.floor := by
  cases x <;> rfl

private theorem floor_div_1024 (d : Int) :
    Model.MathVal.floor (Model.MathVal.div (.int d) (.int 0x400)) = .int (d / 0x400) := by
  rw [floor_mathVal, Model.MathVal.toQ_div, Model.MathVal.toQ_int, Model.MathVal.toQ_int,
    Model.MathVal.rat_floor_div_int d 0x400 (by decide)]

/-- `UTF16EncodeCodePoint`'s steps from after its Assert. -/
theorem utf16Enc_rest [PinsHold] (st : State F) (fr : List (Frame F)) (a : AlgId) (nd : Option F.Node)
    (cp : Int) (h0 : 0 ≤ cp) (h1 : cp ≤ 0x10FFFF) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨a, nd, #[.math (.int cp), .unbound, .unbound], .steps false true true, [1], [], none⟩ :: fr,
        .code (utf16EncCode.drop 2)⟩
      ⟨st, fr, .val (.str (Accel.utf16Units cp.toNat))⟩ := by
  by_cases hle : cp ≤ 0xFFFF
  · have hn : cp.toNat ≤ 0xFFFF := by omega
    simp only [Accel.utf16Units, hn, ↓reduceIte]
    gsteps
    refine Steps.codeIf true (by mdecide) ?_
    gsteps
    mprim (prim_unitOf cp h0 hle _)
    gsteps
    mprim (prim_strOf1 cp h0 hle _)
    gsteps
    exact .refl _
  · have hn : ¬ cp.toNat ≤ 0xFFFF := by omega
    simp only [Accel.utf16Units, hn, ↓reduceIte]
    gsteps
    refine Steps.codeIf false (by mdecide) ?_
    gsteps
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, numeral_hex]
    have hdiv : ((Model.MathVal.int cp).add (Model.MathVal.neg (Model.MathVal.int (65536 : Nat)))).div
        (Model.MathVal.int (1024 : Nat)) =
        Model.MathVal.div (.int (cp + -65536)) (.int 0x400) := rfl
    rw [hdiv, floor_div_1024]
    mprim (prim_unitOf ((cp + -65536) / 1024 + 55296) (by omega) (by omega) _)
    gsteps
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, numeral_hex]
    rw [hdiv, floor_div_1024]
    have hmod : (cp + -65536) + -(1024 * ((cp + -65536) / 1024)) + 56320 = (cp + -65536) % 1024 + 56320 := by
      have := Int.emod_add_mul_ediv (cp + -65536) 1024; omega
    have hpt := prim_unitOf ((cp + -65536) % 1024 + 56320) (by omega) (by omega) st
    rw [← hmod] at hpt
    mprim hpt
    rw [hmod]
    gsteps
    mprim (prim_concat_units ((cp + -65536) / 1024 + 55296) ((cp + -65536) % 1024 + 56320)
      (by omega) (by omega) (by omega) (by omega) _)
    gsteps
    have e1 : ((cp + -65536) / 1024 + 55296).toNat = (cp.toNat - 0x10000) / 0x400 + 0xD800 := by omega
    have e2 : ((cp + -65536) % 1024 + 56320).toNat = (cp.toNat - 0x10000) % 0x400 + 0xDC00 := by omega
    rw [e1, e2]
    exact .refl _

theorem utf16Enc_body [PinsHold] (st : State F) (fr : List (Frame F)) (a : AlgId) (nd : Option F.Node)
    (cp : Int) (h0 : 0 ≤ cp) (h1 : cp ≤ 0x10FFFF) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨a, nd, #[.math (.int cp), .unbound, .unbound], .steps false true true, [], [], none⟩ :: fr,
        .code utf16EncCode⟩
      ⟨st, fr, .val (.str (Accel.utf16Units cp.toNat))⟩ := by
  cases chk
  · mstep; mstep; mstep
    exact utf16Enc_rest H false st fr a nd cp h0 h1
  · iterate 14 gstep
    mprim (prim_chain_cp cp h0 h1 _)
    mstep; mstep; mstep
    exact utf16Enc_rest H true st fr a nd cp h0 h1

theorem utf16Enc_steps [PinsHold] (st : State F) (fr : List (Frame F))
    (cp : Int) (h0 : 0 ≤ cp) (h1 : cp ≤ 0x10FFFF) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, fr, .invoke (.alg ⟨Known.cUTF16EncodeCodePoint, 0⟩ [.math (.int cp)])⟩
      ⟨st, fr, .val (.str (Accel.utf16Units cp.toNat))⟩ := by
  refine Steps.next (step_alg H chk _ _ _ _ _ _ utf16EncAlg_pin utf16EncCode_pin) ?_
  exact utf16Enc_body H chk st fr _ none cp h0 h1

theorem utf16Enc_row [PinsHold] (c : Cfg F) (vs : List (Val F))
    (r : Run F (Option (Val F))) (nd : Option F.Node) (he : utf16EncEntry vs = some r)
    (hstep : step (Ctx.spec Engine.P' H chk) c =
      enterAlg (Ctx.spec Engine.P' H chk) c utf16EncAlg nd (utf16EncAlg.args vs) utf16EncAlg.header.rc true true) :
    Sim (Ctx.spec Engine.P' H chk) c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step (Ctx.spec Engine.P' H chk) c) := by
  unfold utf16EncEntry at he
  split at he
  · rename_i cp
    by_cases hcp : 0 ≤ cp ∧ cp ≤ 0x10FFFF
    · simp only [hcp, and_self, ↓reduceIte, Option.some.injEq] at he
      subst he
      obtain ⟨st, fs, ctl⟩ := c
      have hcode : (Ctx.spec Engine.P' H chk).algCode utf16EncAlg.id = utf16EncCode :=
        algCode_pin H chk _ _ utf16EncCode_pin
      show Steps _ _ _
      refine Steps.next hstep ?_
      rw [hcode]
      exact utf16Enc_body H chk st fs _ nd cp hcp.1 hcp.2
    · simp only [hcp, ↓reduceIte] at he; cases he
  · cases he

theorem utf16Enc_algRow [PinsHold] :
    AlgRow (Ctx.spec Engine.P' H chk) ⟨Known.cUTF16EncodeCodePoint, 0⟩ utf16EncEntry :=
  ⟨utf16EncAlg, utf16EncAlg_pin, fun c vs r nd he hstep => utf16Enc_row H chk c vs r nd he hstep⟩

/-! ## `CodePointsToString` -/

private theorem push_utf16Units (acc : Array UInt16) (n : Nat) :
    (if n ≤ 0xFFFF then acc.push (UInt16.ofNat n)
     else
       let d := n - 0x10000
       (acc.push (UInt16.ofNat (d / 0x400 + 0xD800))).push (UInt16.ofNat (d % 0x400 + 0xDC00))) =
    acc ++ Accel.utf16Units n := by
  by_cases h : n ≤ 0xFFFF
  · simp only [Accel.utf16Units, h, ↓reduceIte]
    rw [Array.push_eq_append]
  · simp only [Accel.utf16Units, h, ↓reduceIte]
    rw [Array.push_eq_append, Array.push_eq_append, Array.append_assoc]
    rfl

def cptsBodyCode : Code :=
  [Ins.site [1, 2],
   Ins.let_ 1 (Op.call (CallK.prim Known.pConcat)
     [Op.var 1, Op.call (CallK.alg ⟨Known.cUTF16EncodeCodePoint, 0⟩) [Op.var 2]])]

theorem cpts_loop [PinsHold] (st : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node)
    (l : Nat) (xs : Array (Val F)) (o : Nat) (hl : st.heap.get l = some (.list xs o)) :
    ∀ (k i : Nat) (acc out : Array UInt16) (v2 : Val F) (q : List Nat) (r : Nat),
      xs.size - i ≤ k →
      encodeCps xs k i acc = some out →
      Steps (Ctx.spec Engine.P' H chk)
        ⟨st, ⟨a, nd, #[.ref l, .str acc, v2], .steps false true true, q,
          [.seq [Ins.site [3], Ins.ret (Op.var 1)]], none⟩ :: fs,
          .loop .round ⟨some 2, Iter.each (Op.var 0) false, [2], cptsBodyCode, .each l (.int i) false, r⟩⟩
        ⟨st, fs, .val (.str out)⟩ := by
  intro k
  induction k with
  | zero =>
    intro i acc out v2 q r hk henc
    have hi : ¬ i < xs.size := by omega
    simp only [encodeCps, Option.some.injEq] at henc
    subst henc
    refine Steps.next (step_each_end _ _ _ _ _ _ _ _ _ _ _ _ hl hi) ?_
    gsteps
    exact .refl _
  | succ k ih =>
    intro i acc out v2 q r hk henc
    by_cases hi : i < xs.size
    · simp only [encodeCps, hi, ↓reduceIte] at henc
      cases hxi : xs[i]? with
      | none => rw [hxi] at henc; cases henc
      | some v =>
        rw [hxi] at henc
        cases v with
        | math mv =>
          cases mv with
          | int cp =>
            by_cases hcp : 0 ≤ cp ∧ cp ≤ 0x10FFFF
            · simp only [hcp, and_self, ↓reduceIte] at henc
              rw [push_utf16Units] at henc
              refine Steps.next (step_each_in _ _ _ _ _ _ _ _ _ _ _ _ _ hl hxi) ?_
              dsimp only [Cfg.setSlot, Cfg.mapTop, loopBody]
              simp only [List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero]
              gsteps
              refine Steps.trans (utf16Enc_steps H chk _ _ cp hcp.1 hcp.2) ?_
              gsteps_round
              rw [utf16_empty, Array.empty_append]
              exact ih (i + 1) (acc ++ Accel.utf16Units cp.toNat) out (.math (.int cp)) [1, 2] (r + 1) (by omega) henc
            · simp only [hcp, ↓reduceIte] at henc; cases henc
          | frac _ _ => cases henc
        | _ => cases henc
    · simp only [encodeCps, hi, ↓reduceIte, Option.some.injEq] at henc
      subst henc
      refine Steps.next (step_each_end _ _ _ _ _ _ _ _ _ _ _ _ hl hi) ?_
      gsteps
      exact .refl _

theorem cpts_steps [PinsHold] (st : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node)
    (l : Nat) (xs : Array (Val F)) (o : Nat) (out : Array UInt16)
    (hl : st.heap.get l = some (.list xs o)) (henc : encodeCps xs xs.size 0 #[] = some out) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨a, nd, #[.ref l, .unbound, .unbound], .steps false true true, [], [], none⟩ :: fs, .code cptsCode⟩
      ⟨st, fs, .val (.str out)⟩ := by
  iterate 5 gstep
  rw [utf16_empty]
  gsteps_round
  exact cpts_loop H chk st fs a nd l xs o hl xs.size 0 #[] out .unbound [2] (0 + 1) (Nat.le_refl _) henc

theorem cpts_row [PinsHold] (c : Cfg F) (vs : List (Val F))
    (r : Run F (Option (Val F))) (nd : Option F.Node) (he : cptsEntry vs = some r)
    (hstep : step (Ctx.spec Engine.P' H chk) c =
      enterAlg (Ctx.spec Engine.P' H chk) c cptsAlg nd (cptsAlg.args vs) cptsAlg.header.rc true true) :
    Sim (Ctx.spec Engine.P' H chk) c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step (Ctx.spec Engine.P' H chk) c) := by
  unfold cptsEntry at he
  split at he
  · rename_i l
    cases Option.some.inj he
    obtain ⟨st, fs, ctl⟩ := c
    unfold bindR cptsRun
    dsimp only
    cases hl : st.heap.get l with
    | none => exact Sim.step _ _
    | some cell =>
      cases cell with
      | list xs o =>
        by_cases hsz : xs.size ≤ scanLimit
        · simp only [hsz, ↓reduceIte]
          cases henc : encodeCps xs xs.size 0 #[] with
          | none => exact Sim.step _ _
          | some out =>
            dsimp only
            have hcode : (Ctx.spec Engine.P' H chk).algCode cptsAlg.id = cptsCode :=
              algCode_pin H chk _ _ cptsCode_pin
            show Steps _ _ _
            refine Steps.next hstep ?_
            rw [hcode]
            exact cpts_steps H chk st fs _ nd l xs o out hl henc
        · simp only [hsz, ↓reduceIte]
          exact Sim.step _ _
      | _ => exact Sim.step _ _
  · cases he

theorem cpts_algRow [PinsHold] :
    AlgRow (Ctx.spec Engine.P' H chk) ⟨Known.cCodePointsToString, 0⟩ cptsEntry :=
  ⟨cptsAlg, cptsAlg_pin, fun c vs r nd he hstep => cpts_row H chk c vs r nd he hstep⟩

end Engine.Machine
