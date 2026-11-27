module

public import Engine.Proofs.Step.Sym
public import Engine.Proofs.Step.Table

@[expose] public section

/-!
# CodePointAt's steps

What StringToCodePoints's row and GetStringIndex's share: CodePointAt (`cpa_steps`: at a String and an index of
it, the Record `Engine.Accel.cpRec (cpAt s p)` in one new cell), which calls UTF16SurrogatePairToCodePoint
(`pair_steps`) and tests the sorts of the surrogates (`lead_steps`, `surr_steps`, `trail_steps`: each an algorithm
of the program, `range_steps`, over the test of the sort of the code units, `cu_steps`). The Record's fields are
`cpRec_cp`, `cpRec_count`; `cpAt_count` bounds the code units it counts. Each unit is pinned here, once.
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-! ## The sorts' definitions in the engine's program -/

set_option maxRecDepth 8000 in
theorem sortDef_98 : Engine.P.sortDef Known.sCodeUnit = some { super := [], test := .alg ⟨Known.cSortCodeUnit, 0⟩, record := false } := by
  rw [sortDef_eq]; rfl

set_option maxRecDepth 8000 in
theorem sortDef_95 : Engine.P.sortDef Known.sLeading = some { super := [], test := .alg ⟨Known.cSortLeading, 0⟩, record := false } := by
  rw [sortDef_eq]; rfl

set_option maxRecDepth 8000 in
theorem sortDef_96 : Engine.P.sortDef Known.sSurrogate = some { super := [Known.sCodeUnit], test := .alg ⟨Known.cSortSurrogate, 0⟩, record := false } := by
  rw [sortDef_eq]; rfl

set_option maxRecDepth 8000 in
theorem sortDef_97 : Engine.P.sortDef Known.sTrailing = some { super := [], test := .alg ⟨Known.cSortTrailing, 0⟩, record := false } := by
  rw [sortDef_eq]; rfl

variable (H : Host F) (chk : Bool)

/-! ## The sorts' tests -/

/-- The steps of the sort test of the code units, at one: true. -/
theorem cu_steps [PinsHold] (s : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (sl : Array (Val F))
    (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (u : Int) (h0 : 0 ≤ u) (h1 : u ≤ 0xFFFF) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .invoke (.sort Known.sCodeUnit (.math (.int u)))⟩
      ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val (.bool true)⟩ := by
  refine Steps.next (step_sort_alg H chk _ _ _ _ _ _ sortDef_98 rfl rfl) ?_
  dsimp only [Cfg.push]
  refine Steps.next (step_alg H chk _ _ _ _ _ _ cuAlg_pin cuCode_pin) ?_
  show Steps _ ⟨s, ⟨_, none, #[.math (.int u)], .steps false true true, [], [], none⟩ :: _, .code cuCode⟩ _
  gsteps
  refine Steps.next (step_sort_int H chk _ _ _) ?_
  gsteps
  refine Steps.valBool true (by mdecide) ?_
  gsteps
  exact .refl _

/-- "the numeric value of" a code point. -/
theorem prim_numericValue (u : Int) (h0 : 0 ≤ u) (h1 : u ≤ 0x10FFFF) (s : State F) :
    Ecma.prim Known.pNumericValue [.math (Model.MathVal.int u)] s = .ok (.math (Model.MathVal.int u)) s := by
  show Prims.Strings.numericValue [.math (Model.MathVal.int u)] s = _
  have hp : Prims.Strings.isPoint (M := F) (Model.MathVal.int u) = true := by
    simp [Prims.Strings.isPoint, Prims.Strings.inRange, Model.MathVal.lt, Model.MathVal.isInt]
    omega
  simp [Prims.Strings.numericValue, hp, Run.pure]

/-- The code of the test of a sort of the code units whose values lie in an interval. -/
def rangeCode (lo hi : Nat) (wl wh : String) : Code :=
  [Ins.site [1],
    Ins.br
      (Op.and
        [(Op.var 0).bind
            (Op.and
              [Op.leaf (Leaf.isTy false false)
                  [(Op.leaf Leaf.used [Op.bound]).bind (Op.or [Op.call (CallK.sort Known.sCodeUnit) [Op.bound]])]]),
          (Op.call (CallK.prim Known.pNumericValue) [Op.bnd 0]).bind
            (Op.and
              [Op.leaf (Leaf.isTy false false)
                  [Op.call (CallK.prim Known.pInInterval)
                      [Op.const (Const.math Sign.none (Mag.num (Numeral.hex lo wl))),
                        Op.const (Const.math Sign.none (Mag.num (Numeral.hex hi wh))), Op.bound]]])])
      [Ins.ret (Op.const (Const.val ValLit.true))] [],
    Ins.site [2], Ins.ret (Op.const (Const.val ValLit.false))]

/-- The steps of such a sort's test, at a code unit: whether its value lies in the interval. -/
theorem range_steps [PinsHold] (k : SortId) (aid : AlgId) (g : Alg) (code : Code) (lo hi : Nat) (wl wh : String) (d : SortDef)
    (hd : Engine.P.sortDef k = some d) (ht : d.test = .alg aid) (hr : d.record = false)
    (hg : Engine.P.alg aid = some g) (hid : g.id = aid) (hc : Engine.P'.alg aid = some code)
    (hcode : code = rangeCode lo hi wl wh)
    (hf : ∀ m : Model.MathVal, algFrame g none (g.args [(.math m : Val F)]) g.header.rc true true =
      ⟨aid, none, #[.math m], .steps false true true, [], [], none⟩)
    (s : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (sl : Array (Val F))
    (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (u : Int) (h0 : 0 ≤ u) (h1 : u ≤ 0xFFFF)
    (b : Bool) (hb : b = true ↔ ((lo : Int) ≤ u ∧ u ≤ (hi : Int))) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .invoke (.sort k (.math (.int u)))⟩
      ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val (.bool b)⟩ := by
  refine Steps.next (step_sort_alg H chk _ _ _ _ _ _ hd ht hr) ?_
  dsimp only [Cfg.push]
  refine Steps.next (step_alg H chk _ _ _ _ _ _ hg (by rw [hid]; exact hc)) ?_
  rw [hf, hcode]
  unfold rangeCode
  gsteps
  refine Steps.trans (cu_steps H chk _ _ _ _ _ _ _ _ _ u h0 h1) ?_
  gsteps
  refine Steps.next (step_prim_ok _ _ _ _ _ _ _ rfl rfl (prim_numericValue u h0 (by omega) _)) ?_
  gsteps
  cases b
  · have hn : ¬ ((lo : Int) ≤ u ∧ u ≤ (hi : Int)) := fun h => by simpa using hb.mpr h
    refine Steps.valBool false (by mdecide) ?_
    gsteps
    exact .refl _
  · refine Steps.valBool true (by have := hb.mp rfl; mdecide) ?_
    gsteps
    exact .refl _

/-- The test of the sort of the leading surrogates, at a code unit. -/
theorem lead_steps [PinsHold] (s : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (sl : Array (Val F))
    (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (u : Int) (h0 : 0 ≤ u) (h1 : u ≤ 0xFFFF)
    (b : Bool) (hb : b = true ↔ (0xD800 ≤ u ∧ u ≤ 0xDBFF)) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .invoke (.sort Known.sLeading (.math (.int u)))⟩
      ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val (.bool b)⟩ :=
  range_steps H chk Known.sLeading ⟨Known.cSortLeading, 0⟩ leadAlg leadCode 0xD800 0xDBFF "D800" "DBFF" _ sortDef_95 rfl rfl leadAlg_pin rfl
    leadCode_pin rfl (fun _ => rfl) s fs a nd sl kd p K ci u h0 h1 b hb

/-- The test of the sort of the surrogates, at a code unit. -/
theorem surr_steps [PinsHold] (s : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (sl : Array (Val F))
    (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (u : Int) (h0 : 0 ≤ u) (h1 : u ≤ 0xFFFF)
    (b : Bool) (hb : b = true ↔ (0xD800 ≤ u ∧ u ≤ 0xDFFF)) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .invoke (.sort Known.sSurrogate (.math (.int u)))⟩
      ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val (.bool b)⟩ :=
  range_steps H chk Known.sSurrogate ⟨Known.cSortSurrogate, 0⟩ unitAlg unitCode 0xD800 0xDFFF "D800" "DFFF" _ sortDef_96 rfl rfl unitAlg_pin rfl
    unitCode_pin rfl (fun _ => rfl) s fs a nd sl kd p K ci u h0 h1 b hb

/-- The test of the sort of the trailing surrogates, at a code unit. -/
theorem trail_steps [PinsHold] (s : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (sl : Array (Val F))
    (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (u : Int) (h0 : 0 ≤ u) (h1 : u ≤ 0xFFFF)
    (b : Bool) (hb : b = true ↔ (0xDC00 ≤ u ∧ u ≤ 0xDFFF)) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .invoke (.sort Known.sTrailing (.math (.int u)))⟩
      ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val (.bool b)⟩ :=
  range_steps H chk Known.sTrailing ⟨Known.cSortTrailing, 0⟩ trailAlg trailCode 0xDC00 0xDFFF "DC00" "DFFF" _ sortDef_97 rfl rfl trailAlg_pin rfl
    trailCode_pin rfl (fun _ => rfl) s fs a nd sl kd p K ci u h0 h1 b hb

/-! ## The String primitives and UTF16SurrogatePairToCodePoint -/

/-- "the code point whose numeric value is" a code point's. -/
theorem prim_pointOf (u : Int) (h0 : 0 ≤ u) (h1 : u ≤ 0x10FFFF) (s : State F) :
    Ecma.prim Known.pUnitOrPointOf [.choice 0, .math (Model.MathVal.int u)] s = .ok (.math (Model.MathVal.int u)) s := by
  show Prims.Strings.unitOrPointOf [.choice 0, .math (Model.MathVal.int u)] s = _
  have hp : Prims.Strings.isPoint (M := F) (Model.MathVal.int u) = true := by
    simp [Prims.Strings.isPoint, Prims.Strings.inRange, Model.MathVal.lt, Model.MathVal.isInt]
    omega
  simp [Prims.Strings.unitOrPointOf, hp, Run.pure]

/-- "the code unit at index p within s", at an index of s. -/
theorem prim_unitAt (t : Array UInt16) (p : Nat) (hp : p < t.size) (s : State F) :
    Ecma.prim Known.pUnitAt [.math (Model.MathVal.int p), .str t] s =
      .ok (.math (Model.MathVal.int ((t[p]?.getD 0).toNat : Nat))) s := by
  show Prims.Strings.unitAt [.math (Model.MathVal.int p), .str t] s = _
  simp [Prims.Strings.unitAt, Prims.Strings.units, bind, Run.bind, Run.Res.bind, Run.pure, Model.MathVal.idx, hp]

/-- UTF16SurrogatePairToCodePoint's steps at a leading and a trailing surrogate. -/
theorem pair_steps [PinsHold] (s : State F) (fr : List (Frame F)) (l t : Int)
    (hl0 : 0xD800 ≤ l) (hl1 : l ≤ 0xDBFF) (ht0 : 0xDC00 ≤ t) (ht1 : t ≤ 0xDFFF) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨Known.cUTF16SurrogatePair, 0⟩ [.math (.int l), .math (.int t)])⟩
      ⟨s, fr, .val (.math (Model.MathVal.int ((l - 0xD800) * 0x400 + (t - 0xDC00) + 0x10000)))⟩ := by
  refine Steps.next (step_alg H chk _ _ _ _ _ _ pairAlg_pin pairCode_pin) ?_
  show Steps _ ⟨s, ⟨_, none, #[.math (.int l), .math (.int t), .unbound], .steps false true true, [], [], none⟩ :: _,
    .code pairCode⟩ _
  cases chk
  · gsteps
    show Steps _ ⟨_, _, .invoke (.prim Known.pUnitOrPointOf [.choice 0, (.math (Model.MathVal.int ((l - 0xD800) * 0x400 + (t - 0xDC00) + 0x10000)) : Val F)])⟩ _
    refine Steps.next (step_prim_ok _ _ _ _ _ _ _ rfl rfl (prim_pointOf _ (by omega) (by omega) _)) ?_
    gsteps
    exact .refl _
  · gsteps
    refine Steps.trans (lead_steps H true _ _ _ _ _ _ _ _ _ l (by omega) (by omega) true (by simp; omega)) ?_
    gsteps
    refine Steps.trans (surr_steps H true _ _ _ _ _ _ _ _ _ l (by omega) (by omega) true (by simp; omega)) ?_
    gsteps
    refine Steps.trans (trail_steps H true _ _ _ _ _ _ _ _ _ t (by omega) (by omega) true (by simp; omega)) ?_
    gsteps
    refine Steps.trans (surr_steps H true _ _ _ _ _ _ _ _ _ t (by omega) (by omega) true (by simp; omega)) ?_
    gsteps
    show Steps _ ⟨_, _, .invoke (.prim Known.pUnitOrPointOf [.choice 0, (.math (Model.MathVal.int ((l - 0xD800) * 0x400 + (t - 0xDC00) + 0x10000)) : Val F)])⟩ _
    refine Steps.next (step_prim_ok _ _ _ _ _ _ _ rfl rfl (prim_pointOf _ (by omega) (by omega) _)) ?_
    gsteps
    exact .refl _

/-! ## CodePointAt -/

macro "mlead" u:term:max b:term:max : tactic =>
  `(tactic| refine Steps.trans (lead_steps _ _ _ _ _ _ _ _ _ _ _ $u (by omega) (by omega) $b (by simp; omega)) ?_)

macro "msurr" u:term:max b:term:max : tactic =>
  `(tactic| refine Steps.trans (surr_steps _ _ _ _ _ _ _ _ _ _ _ $u (by omega) (by omega) $b (by simp; omega)) ?_)

macro "mtrail" u:term:max b:term:max : tactic =>
  `(tactic| refine Steps.trans (trail_steps _ _ _ _ _ _ _ _ _ _ _ $u (by omega) (by omega) $b (by simp; omega)) ?_)

open Engine.Accel in
/-- CodePointAt's steps from its read of the code unit at the position. -/
theorem cpa_rest [PinsHold] (st : State F) (fr : List (Frame F)) (s : Array UInt16) (p : Nat) (hp : p < s.size) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨cpaAlg.id, none, #[.str s, .math (.int p), .math (.int s.size), .unbound, .unbound, .unbound],
        .steps false true true, [3], [.args (.let_ 3) [] [], .seq (cpaCode.drop 6)], none⟩ :: fr,
        .invoke (.prim Known.pUnitAt [.math (.int p), .str s])⟩
      ⟨{ st with heap := st.heap.push (cpRec (cpAt s p)) }, fr, .val (.ref st.heap.next)⟩ := by
  mprim (prim_unitAt s p hp _)
  obtain ⟨u, hu⟩ : ∃ u : Int, u = ((s[p]?.getD 0).toNat : Nat) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by omega
  have hu1 : u ≤ 0xFFFF := by
    have := (s[p]?.getD 0).toNat_lt
    omega
  unfold cpAt
  simp only [← hu]
  gsteps
  mprim (prim_numericValue u hu0 (by omega) _)
  gsteps
  mprim (prim_pointOf u hu0 (by omega) _)
  gsteps
  by_cases h1 : u < 0xD800 ∨ 0xDFFF < u
  · simp only [h1, ↓reduceIte]
    mlead u false
    gsteps
    mtrail u false
    gsteps
    exact .refl _
  simp only [h1, ↓reduceIte]
  by_cases hB : 0xDC00 ≤ u
  · have h2 : 0xDC00 ≤ u ∨ p + 1 = s.size := .inl hB
    simp only [h2, ↓reduceIte]
    mlead u false
    gsteps
    mtrail u true
    gsteps
    msurr u true
    gsteps
    mtrail u true
    gsteps
    msurr u true
    gsteps
    exact .refl _
  mlead u true
  gsteps
  msurr u true
  gsteps
  mtrail u false
  gsteps
  by_cases hC : p + 1 = s.size
  · have h2 : 0xDC00 ≤ u ∨ p + 1 = s.size := .inr hC
    simp only [h2, ↓reduceIte]
    refine Steps.valBool true (by mdecide) ?_
    gsteps
    exact .refl _
  have h2 : ¬ (0xDC00 ≤ u ∨ p + 1 = s.size) := by omega
  simp only [h2, ↓reduceIte]
  refine Steps.valBool false (by mdecide) ?_
  gsteps
  show Steps _ ⟨_, _, .invoke (.prim Known.pUnitAt [(.math (Model.MathVal.int ((p + 1 : Nat) : Int)) : Val F), .str s])⟩ _
  mprim (prim_unitAt s (p + 1) (by omega) _)
  obtain ⟨v, hv⟩ : ∃ v : Int, v = ((s[p + 1]?.getD 0).toNat : Nat) := ⟨_, rfl⟩
  have hv0 : 0 ≤ v := by omega
  have hv1 : v ≤ 0xFFFF := by
    have := (s[p + 1]?.getD 0).toNat_lt
    omega
  simp only [← hv]
  gsteps
  by_cases h3 : v < 0xDC00 ∨ 0xDFFF < v
  · simp only [h3, ↓reduceIte]
    mtrail v false
    gsteps
    exact .refl _
  simp only [h3, ↓reduceIte]
  mtrail v true
  gsteps
  msurr v true
  gsteps
  refine Steps.trans (pair_steps _ _ _ _ u v (by omega) (by omega) (by omega) (by omega)) ?_
  gsteps
  exact .refl _

open Engine.Accel in
theorem cpa_steps [PinsHold] (st : State F) (fr : List (Frame F)) (s : Array UInt16) (p : Nat) (hp : p < s.size) :
    Steps (Ctx.spec Engine.P' H chk) ⟨st, fr, .invoke (.alg ⟨Known.cCodePointAt, 0⟩ [.str s, .math (.int p)])⟩
      ⟨{ st with heap := st.heap.push (cpRec (cpAt s p)) }, fr, .val (.ref st.heap.next)⟩ := by
  refine Steps.next (step_alg H chk _ _ _ _ _ _ cpaAlg_pin cpaCode_pin) ?_
  show Steps _ ⟨st, ⟨_, none, #[.str s, .math (.int p), .unbound, .unbound, .unbound, .unbound],
    .steps false true true, [], [], none⟩ :: _, .code cpaCode⟩ _
  cases chk
  · gsteps
    exact cpa_rest H false st fr s p hp
  · gsteps
    refine Steps.valBool true (by mdecide) ?_
    gsteps
    refine Steps.valBool true (by mdecide) ?_
    gsteps
    exact cpa_rest H true st fr s p hp

/-! ## CodePointAt's Record -/

open Engine.Accel in
/-- [[CodePoint]] of CodePointAt's Record. -/
theorem cpRec_cp (st : State F) (a : Nat) (t : Int × Nat × Bool) (h : st.heap.get a = some (cpRec t)) :
    readField (.ref a) Known.fCodePoint st = .ok (.math (Model.MathVal.int t.1)) st := by
  have e : (F.recGet (F.recSet (F.recSet (F.recSet F.recEmpty Known.fCodePoint (.math (Model.MathVal.int t.1))) Known.fCodeUnitCount
      (.math (Model.MathVal.int t.2.1))) Known.fIsUnpairedSurrogate (.bool t.2.2)) Known.fCodePoint : Option (Val F)) =
      some (.math (Model.MathVal.int t.1)) := by
    show Model.WMap.get (Model.WMap.put (Model.WMap.put (Model.WMap.put _ _ _) _ _) _ _) _ = _
    simp [Engine.Impl.wget_put, Known.fCodePoint, Known.fCodeUnitCount, Known.fIsUnpairedSurrogate]
  have hc : readCell a st = .ok (cpRec t) st := by simp only [readCell, Impl, h]
  show Run.Res.bind (readCell a st) _ = _
  rw [hc]
  show optOr .sortError (F.recGet _ _) st = _
  rw [e]
  rfl

open Engine.Accel in
/-- [[CodeUnitCount]] of CodePointAt's Record. -/
theorem cpRec_count (st : State F) (a : Nat) (t : Int × Nat × Bool) (h : st.heap.get a = some (cpRec t)) :
    readField (.ref a) Known.fCodeUnitCount st = .ok (.math (Model.MathVal.int t.2.1)) st := by
  have e : (F.recGet (F.recSet (F.recSet (F.recSet F.recEmpty Known.fCodePoint (.math (Model.MathVal.int t.1))) Known.fCodeUnitCount
      (.math (Model.MathVal.int t.2.1))) Known.fIsUnpairedSurrogate (.bool t.2.2)) Known.fCodeUnitCount : Option (Val F)) =
      some (.math (Model.MathVal.int t.2.1)) := by
    show Model.WMap.get (Model.WMap.put (Model.WMap.put (Model.WMap.put _ _ _) _ _) _ _) _ = _
    simp [Engine.Impl.wget_put, Known.fCodePoint, Known.fCodeUnitCount, Known.fIsUnpairedSurrogate]
  have hc : readCell a st = .ok (cpRec t) st := by simp only [readCell, Impl, h]
  show Run.Res.bind (readCell a st) _ = _
  rw [hc]
  show optOr .sortError (F.recGet _ _) st = _
  rw [e]
  rfl

open Engine.Accel in
/-- CodePointAt's code unit count: one or two, within the String. -/
theorem cpAt_count (s : Array UInt16) (p : Nat) (hp : p < s.size) :
    1 ≤ (cpAt s p).2.1 ∧ p + (cpAt s p).2.1 ≤ s.size := by
  by_cases hA : (((s[p]?.getD 0).toNat : Nat) : Int) < 0xD800 ∨ 0xDFFF < (((s[p]?.getD 0).toNat : Nat) : Int)
  · have hc : cpAt s p = ((((s[p]?.getD 0).toNat : Nat) : Int), 1, false) := by
      unfold cpAt; exact if_pos hA
    rw [hc]
    exact ⟨Nat.le_refl 1, hp⟩
  · by_cases hCE : 0xDC00 ≤ (((s[p]?.getD 0).toNat : Nat) : Int) ∨ p + 1 = s.size
    · have hc : cpAt s p = ((((s[p]?.getD 0).toNat : Nat) : Int), 1, true) := by
        unfold cpAt; exact (if_neg hA).trans (if_pos hCE)
      rw [hc]
      exact ⟨Nat.le_refl 1, hp⟩
    · have h2 : p + 2 ≤ s.size := by omega
      by_cases hS : (((s[p + 1]?.getD 0).toNat : Nat) : Int) < 0xDC00 ∨ 0xDFFF < (((s[p + 1]?.getD 0).toNat : Nat) : Int)
      · have hc : cpAt s p = ((((s[p]?.getD 0).toNat : Nat) : Int), 1, true) := by
          unfold cpAt; exact (if_neg hA).trans ((if_neg hCE).trans (if_pos hS))
        rw [hc]
        exact ⟨Nat.le_refl 1, hp⟩
      · have hc : cpAt s p = (((((s[p]?.getD 0).toNat : Nat) : Int) - 0xD800) * 0x400 +
            ((((s[p + 1]?.getD 0).toNat : Nat) : Int) - 0xDC00) + 0x10000, 2, false) := by
          unfold cpAt; exact (if_neg hA).trans ((if_neg hCE).trans (if_neg hS))
        rw [hc]
        exact ⟨Nat.le_succ 1, h2⟩

end Engine.Machine
