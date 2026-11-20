module

public import Engine.Machine
public import Engine.Proofs.Pins.Eq
meta import Engine.Proofs.Pins.Pin
meta import Engine.Machine

@[expose] public section

/-!
# Runtime checks of the pinned specification units

The 55 assertions the accelerator proofs depend on (`containsRowsCheck` and the 54 algorithm/code equalities) are
defined as runtime Boolean checks (`pin_alg_def`, `pin_prog_alg_def`) instead of `native_decide` axioms. `Engine.setupAt`
consults `pinsOkThunk.get` when `accel` is enabled and falls back to `Engine.Machine.plain` otherwise; `pinsHold_of_ok`
delivers all 55 equations (`PinsHold`) on the enabled branch without any axiom beyond Lean's standard three.
-/

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Pins

/-! ## Contains row shapes and check -/

/-- A row that returns *false*. -/
def containsRetCode : Code := [.site [1], .ret (.const (.val .false))]

/-- `If child Contains symbol is true, return true. Return false.` -/
def containsAny1Code (k : NtId) : Code :=
  [Ins.site [1],
   Ins.br
    ((Op.call (CallK.alg { clause := 2725, idx := 0 }) [Op.child 5 k, Op.bnd 0]).bind
      (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.val ValLit.true)]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [2], Ins.ret (Op.const (Const.val ValLit.false))]

/-- `Return the result of ComputedPropertyContains of child with argument symbol.` -/
def containsCpc1Code (k : NtId) : Code :=
  [Ins.site [1],
   Ins.ret (Op.call (CallK.alg { clause := 2562, idx := 0 }) [Op.on (OnK.sdo 24) (Op.child 5 k) [Op.var 0]])]

/-- `Return the result of child Contains symbol.` (ComputedPropertyContains of a computed name). -/
def containsCpcPhCode (k : NtId) : Code :=
  [Ins.site [1],
   Ins.ret
    (Op.call (CallK.alg { clause := 2562, idx := 0 })
      [Op.call (CallK.alg { clause := 2725, idx := 0 }) [Op.child 5 k, Op.bnd 0]])]

/-- ComputedPropertyContains of two children in turn. -/
def containsCpc2Code (k1 k2 : NtId) : Code :=
  [Ins.site [1], Ins.let_ 1 (Op.on (OnK.sdo 24) (Op.child 5 k1) [Op.var 0]), Ins.site [2],
   Ins.br ((Op.var 1).bind (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.val ValLit.true)]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [3],
   Ins.ret (Op.call (CallK.alg { clause := 2562, idx := 0 }) [Op.on (OnK.sdo 24) (Op.child 5 k2) [Op.var 0]])]

/-- `If symbol is |K|, return true. Return ComputedPropertyContains of |K| with argument symbol.` -/
def containsIsSymCode (k : NtId) : Code :=
  [.site [1],
   .br ((Op.var 0).bind (.and [.leaf (.isVal false false) [.bound, .const (.nt k [])]]))
     [.ret (.const (.val .true))] [],
   .site [2],
   .ret (.call (.alg ⟨2562, 0⟩) [.on (.sdo 24) (.child 5 k) [.var 0]])]

/-- `If symbol is the |ReservedWord| super, return true. Return false.` -/
def containsSuperCode : Code :=
  [Ins.site [1],
   Ins.br
    ((Op.var 0).bind
      (Op.and
        [Op.leaf (Leaf.isVal false false)
            [Op.bound,
              Op.call (CallK.alg { clause := 2728, idx := 0 })
                [Op.const (Const.nt 37 []), Op.const (Const.term "super")]]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [2], Ins.ret (Op.const (Const.val ValLit.false))]

/-- An arrow function's parameters and body. -/
def containsArrow2Code : Code :=
  [Ins.site [1],
   Ins.br
    ((Op.var 0).bind
      (Op.and
        [Op.leaf (Leaf.isVal true false)
            [Op.bound, Op.const (Const.nt 140 []), Op.const (Const.nt 138 []), Op.const (Const.nt 144 []),
              Op.const (Const.term "super"), Op.const (Const.term "this")]]))
    [Ins.ret (Op.const (Const.val ValLit.false))] [],
   Ins.site [2],
   Ins.br
    ((Op.call (CallK.alg { clause := 2725, idx := 0 }) [Op.child 5 251, Op.bnd 0]).bind
      (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.val ValLit.true)]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [3], Ins.ret (Op.call (CallK.alg { clause := 2725, idx := 0 }) [Op.child 5 252, Op.bnd 0])]

/-- An arrow function's body. -/
def containsArrow1Code : Code :=
  [Ins.site [1],
   Ins.br
    ((Op.var 0).bind
      (Op.and
        [Op.leaf (Leaf.isVal true false)
            [Op.bound, Op.const (Const.nt 140 []), Op.const (Const.nt 138 []), Op.const (Const.nt 144 []),
              Op.const (Const.term "super"), Op.const (Const.term "this")]]))
    [Ins.ret (Op.const (Const.val ValLit.false))] [],
   Ins.site [2], Ins.ret (Op.call (CallK.alg { clause := 2725, idx := 0 }) [Op.child 5 284, Op.bnd 0])]

/-- An async arrow function's head, a cover: only the symbol's test is the walk's. -/
def containsArrowDeclCode : Code :=
  [Ins.site [1],
   Ins.br
    ((Op.var 0).bind
      (Op.and
        [Op.leaf (Leaf.isVal true false)
            [Op.bound, Op.const (Const.nt 140 []), Op.const (Const.nt 138 []), Op.const (Const.nt 144 []),
              Op.const (Const.term "super"), Op.const (Const.term "this")]]))
    [Ins.ret (Op.const (Const.val ValLit.false))] [],
   Ins.site [2], Ins.let_ 1 (Op.call (CallK.prim 80) [Op.const (Const.nt 287 []), Op.child 5 286]), Ins.site [3],
   Ins.br
    ((Op.call (CallK.alg { clause := 2725, idx := 0 }) [Op.bnd 1, Op.bnd 0]).bind
      (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.val ValLit.true)]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [4], Ins.ret (Op.call (CallK.alg { clause := 2725, idx := 0 }) [Op.child 5 284, Op.bnd 0])]

def containsClassTailCode : Code :=
  [Ins.site [1],
   Ins.br ((Op.var 0).bind (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.nt 270 [])]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [2],
   Ins.br ((Op.var 0).bind (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.nt 269 [])]]))
    [Ins.site [1, 2],
      Ins.br ((Op.child 5 269).bind (Op.and [Op.leaf (Leaf.isTy false false) [Op.call (CallK.prim 69) [Op.bound]]]))
        [Ins.ret (Op.const (Const.val ValLit.true))] [],
      Ins.site [2, 2], Ins.ret (Op.const (Const.val ValLit.false))]
    [],
   Ins.site [3],
   Ins.br ((Op.child 5 269).bind (Op.and [Op.leaf (Leaf.isTy false false) [Op.call (CallK.prim 69) [Op.bound]]]))
    [Ins.site [1, 3],
      Ins.br
        ((Op.call (CallK.alg { clause := 2725, idx := 0 }) [Op.child 5 269, Op.bnd 0]).bind
          (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.val ValLit.true)]]))
        [Ins.ret (Op.const (Const.val ValLit.true))] []]
    [],
   Ins.site [4],
   Ins.ret (Op.call (CallK.alg { clause := 2562, idx := 0 }) [Op.on (OnK.sdo 24) (Op.child 5 270) [Op.var 0]])]

/-- Each row of Contains and ComputedPropertyContains the walk does not decline at: its variables' count, its
code. -/
def containsShapes : List (AlgId × Nat × Code) :=
  [(⟨322, 1⟩, 1, containsRetCode),
   (⟨322, 2⟩, 1, containsClassTailCode),
   (⟨322, 3⟩, 1, containsRetCode),
   (⟨322, 4⟩, 1, containsArrow2Code),
   (⟨322, 6⟩, 1, containsArrow1Code),
   (⟨322, 7⟩, 2, containsArrowDeclCode),
   (⟨322, 8⟩, 1, containsIsSymCode 255),
   (⟨322, 9⟩, 1, containsRetCode),
   (⟨322, 10⟩, 1, containsAny1Code 137),
   (⟨322, 11⟩, 1, containsSuperCode),
   (⟨322, 12⟩, 1, containsAny1Code 143),
   (⟨322, 13⟩, 1, containsRetCode),
   (⟨322, 14⟩, 1, containsAny1Code 149),
   (⟨323, 0⟩, 1, containsRetCode),
   (⟨323, 1⟩, 1, containsCpcPhCode 130),
   (⟨323, 2⟩, 1, containsCpc1Code 274),
   (⟨323, 3⟩, 1, containsCpc1Code 274),
   (⟨323, 4⟩, 1, containsCpc1Code 274),
   (⟨323, 5⟩, 2, containsCpc2Code 271 272),
   (⟨323, 6⟩, 1, containsRetCode),
   (⟨323, 7⟩, 1, containsRetCode),
   (⟨323, 8⟩, 1, containsCpc1Code 274),
   (⟨323, 9⟩, 1, containsCpc1Code 274)]

/-- The check of the program's row table: at each key of Contains or ComputedPropertyContains whose row has an
id of `containsShapes`, the row has that many variables and the key's code is that code. -/
def containsRowsCheck : Bool :=
  Spec.src.expandMacros.rowMap.keys.all fun (s, k) => !(s == 23 || s == 24) ||
    (match Engine.P.row s k with
    | none => true
    | some r => match containsShapes.lookup r.id with
      | none => true
      | some (n, code) => r.vars.size == n && Code.optEqB (Engine.P'.row s k) (some code))

/-! ## Pinned specification units and Boolean tests -/

-- Exact algorithm rows (6)
pin_alg_def isWriteCode ⟨2775, 0⟩
pin_prog_alg_def isWriteAlg ⟨2775, 0⟩
pin_alg_def stcpCode ⟨573, 0⟩
pin_prog_alg_def stcpAlg ⟨573, 0⟩
pin_alg_def gsiCode ⟨1548, 0⟩
pin_prog_alg_def gsiAlg ⟨1548, 0⟩

-- CodePointAt and surrogate/code-unit sorts (12)
pin_alg_def cpaCode ⟨572, 0⟩
pin_prog_alg_def cpaAlg ⟨572, 0⟩
pin_alg_def pairCode ⟨571, 0⟩
pin_prog_alg_def pairAlg ⟨571, 0⟩
pin_alg_def unitCode ⟨2824, 0⟩
pin_prog_alg_def unitAlg ⟨2824, 0⟩
pin_alg_def leadCode ⟨2825, 0⟩
pin_prog_alg_def leadAlg ⟨2825, 0⟩
pin_alg_def trailCode ⟨2826, 0⟩
pin_prog_alg_def trailAlg ⟨2826, 0⟩
pin_alg_def cuCode ⟨2823, 0⟩
pin_prog_alg_def cuAlg ⟨2823, 0⟩

-- Contains helpers (8 + containsRowsCheck)
pin_alg_def containsDfltCode ⟨322, 0⟩
pin_prog_alg_def containsDfltAlg ⟨322, 0⟩
pin_alg_def containsPhCode ⟨2725, 0⟩
pin_prog_alg_def containsPhAlg ⟨2725, 0⟩
pin_alg_def containsResCode ⟨2562, 0⟩
pin_prog_alg_def containsResAlg ⟨2562, 0⟩
pin_alg_def containsTermCode ⟨2728, 0⟩
pin_prog_alg_def containsTermAlg ⟨2728, 0⟩

-- Number::toString helpers (12)
pin_alg_def toStringCode ⟨117, 0⟩
pin_prog_alg_def toStringAlg ⟨117, 0⟩
pin_alg_def tsReprCode ⟨2633, 0⟩
pin_prog_alg_def tsReprAlg ⟨2633, 0⟩
pin_alg_def tsKDigitsCode ⟨2637, 0⟩
pin_prog_alg_def tsKDigitsAlg ⟨2637, 0⟩
pin_alg_def tsUnitsCode ⟨2641, 0⟩
pin_prog_alg_def tsUnitsAlg ⟨2641, 0⟩
pin_alg_def tsStrOfCode ⟨2671, 0⟩
pin_prog_alg_def tsStrOfAlg ⟨2671, 0⟩
pin_alg_def tsOccCode ⟨2700, 0⟩
pin_prog_alg_def tsOccAlg ⟨2700, 0⟩

-- LoopSkip algorithms (16)
pin_alg_def lsToStringCode ⟨208, 0⟩
pin_prog_alg_def lsToStringAlg ⟨208, 0⟩
pin_alg_def lsHasPropertyCode ⟨242, 0⟩
pin_prog_alg_def lsHasPropertyAlg ⟨242, 0⟩
pin_alg_def lsOrdHasCode ⟨452, 0⟩
pin_prog_alg_def lsOrdHasAlg ⟨452, 0⟩
pin_alg_def lsOrdGopCode ⟨446, 0⟩
pin_prog_alg_def lsOrdGopAlg ⟨446, 0⟩
pin_alg_def lsOrdGpoCode ⟨438, 0⟩
pin_prog_alg_def lsOrdGpoAlg ⟨438, 0⟩
pin_alg_def lsOhpCode ⟨453, 0⟩
pin_prog_alg_def lsOhpAlg ⟨453, 0⟩
pin_alg_def lsOgopCode ⟨447, 0⟩
pin_prog_alg_def lsOgopAlg ⟨447, 0⟩
pin_alg_def lsOgpoCode ⟨439, 0⟩
pin_prog_alg_def lsOgpoAlg ⟨439, 0⟩

/-- Named list of all 55 pin checks (`ecma-run --check-pins`). -/
def pinChecks : List (String × (Unit → Bool)) :=
  [("containsRows", fun _ => containsRowsCheck),
   ("isWriteCode", fun _ => isWriteCode_ok),
   ("isWriteAlg", fun _ => isWriteAlg_ok),
   ("stcpCode", fun _ => stcpCode_ok),
   ("stcpAlg", fun _ => stcpAlg_ok),
   ("gsiCode", fun _ => gsiCode_ok),
   ("gsiAlg", fun _ => gsiAlg_ok),
   ("cpaCode", fun _ => cpaCode_ok),
   ("cpaAlg", fun _ => cpaAlg_ok),
   ("pairCode", fun _ => pairCode_ok),
   ("pairAlg", fun _ => pairAlg_ok),
   ("unitCode", fun _ => unitCode_ok),
   ("unitAlg", fun _ => unitAlg_ok),
   ("leadCode", fun _ => leadCode_ok),
   ("leadAlg", fun _ => leadAlg_ok),
   ("trailCode", fun _ => trailCode_ok),
   ("trailAlg", fun _ => trailAlg_ok),
   ("cuCode", fun _ => cuCode_ok),
   ("cuAlg", fun _ => cuAlg_ok),
   ("containsDfltCode", fun _ => containsDfltCode_ok),
   ("containsDfltAlg", fun _ => containsDfltAlg_ok),
   ("containsPhCode", fun _ => containsPhCode_ok),
   ("containsPhAlg", fun _ => containsPhAlg_ok),
   ("containsResCode", fun _ => containsResCode_ok),
   ("containsResAlg", fun _ => containsResAlg_ok),
   ("containsTermCode", fun _ => containsTermCode_ok),
   ("containsTermAlg", fun _ => containsTermAlg_ok),
   ("toStringCode", fun _ => toStringCode_ok),
   ("toStringAlg", fun _ => toStringAlg_ok),
   ("tsReprCode", fun _ => tsReprCode_ok),
   ("tsReprAlg", fun _ => tsReprAlg_ok),
   ("tsKDigitsCode", fun _ => tsKDigitsCode_ok),
   ("tsKDigitsAlg", fun _ => tsKDigitsAlg_ok),
   ("tsUnitsCode", fun _ => tsUnitsCode_ok),
   ("tsUnitsAlg", fun _ => tsUnitsAlg_ok),
   ("tsStrOfCode", fun _ => tsStrOfCode_ok),
   ("tsStrOfAlg", fun _ => tsStrOfAlg_ok),
   ("tsOccCode", fun _ => tsOccCode_ok),
   ("tsOccAlg", fun _ => tsOccAlg_ok),
   ("lsToStringCode", fun _ => lsToStringCode_ok),
   ("lsToStringAlg", fun _ => lsToStringAlg_ok),
   ("lsHasPropertyCode", fun _ => lsHasPropertyCode_ok),
   ("lsHasPropertyAlg", fun _ => lsHasPropertyAlg_ok),
   ("lsOrdHasCode", fun _ => lsOrdHasCode_ok),
   ("lsOrdHasAlg", fun _ => lsOrdHasAlg_ok),
   ("lsOrdGopCode", fun _ => lsOrdGopCode_ok),
   ("lsOrdGopAlg", fun _ => lsOrdGopAlg_ok),
   ("lsOrdGpoCode", fun _ => lsOrdGpoCode_ok),
   ("lsOrdGpoAlg", fun _ => lsOrdGpoAlg_ok),
   ("lsOhpCode", fun _ => lsOhpCode_ok),
   ("lsOhpAlg", fun _ => lsOhpAlg_ok),
   ("lsOgopCode", fun _ => lsOgopCode_ok),
   ("lsOgopAlg", fun _ => lsOgopAlg_ok),
   ("lsOgpoCode", fun _ => lsOgpoCode_ok),
   ("lsOgpoAlg", fun _ => lsOgpoAlg_ok)]

/-- Names of any failed pin checks. -/
def failedPins : List String :=
  pinChecks.filterMap fun (n, f) => if f () then none else some n

def exactPinsOk : Bool :=
  isWriteCode_ok && isWriteAlg_ok && stcpCode_ok && stcpAlg_ok && gsiCode_ok && gsiAlg_ok

def cpPinsOk : Bool :=
  cpaCode_ok && cpaAlg_ok && pairCode_ok && pairAlg_ok && unitCode_ok && unitAlg_ok &&
  leadCode_ok && leadAlg_ok && trailCode_ok && trailAlg_ok && cuCode_ok && cuAlg_ok

def containsPinsOk : Bool :=
  containsRowsCheck && containsDfltCode_ok && containsDfltAlg_ok && containsPhCode_ok && containsPhAlg_ok &&
  containsResCode_ok && containsResAlg_ok && containsTermCode_ok && containsTermAlg_ok

def numIdxPinsOk : Bool :=
  toStringCode_ok && toStringAlg_ok && tsReprCode_ok && tsReprAlg_ok && tsKDigitsCode_ok && tsKDigitsAlg_ok &&
  tsUnitsCode_ok && tsUnitsAlg_ok && tsStrOfCode_ok && tsStrOfAlg_ok && tsOccCode_ok && tsOccAlg_ok

def roundPinsOk : Bool :=
  lsToStringCode_ok && lsToStringAlg_ok && lsHasPropertyCode_ok && lsHasPropertyAlg_ok &&
  lsOrdHasCode_ok && lsOrdHasAlg_ok && lsOrdGopCode_ok && lsOrdGopAlg_ok &&
  lsOrdGpoCode_ok && lsOrdGpoAlg_ok && lsOhpCode_ok && lsOhpAlg_ok &&
  lsOgopCode_ok && lsOgopAlg_ok && lsOgpoCode_ok && lsOgpoAlg_ok

/-- Whether all 55 pin assertions hold at runtime. -/
def pinsOk : Bool :=
  exactPinsOk && cpPinsOk && containsPinsOk && numIdxPinsOk && roundPinsOk

/-- Lazy process-wide check of `pinsOk` (evaluated at most once when shortcuts are enabled). -/
def pinsOkThunk : Thunk Bool := Thunk.mk fun _ => pinsOk

/-- Hypothesis carrying all 55 pinned program equations when `pinsOk = true`. -/
class PinsHold : Prop where
  containsRows_true : containsRowsCheck = true
  isWriteCode_pin : Engine.P'.alg ⟨2775, 0⟩ = some isWriteCode
  isWriteAlg_pin : Engine.P.alg ⟨2775, 0⟩ = some isWriteAlg
  stcpCode_pin : Engine.P'.alg ⟨573, 0⟩ = some stcpCode
  stcpAlg_pin : Engine.P.alg ⟨573, 0⟩ = some stcpAlg
  gsiCode_pin : Engine.P'.alg ⟨1548, 0⟩ = some gsiCode
  gsiAlg_pin : Engine.P.alg ⟨1548, 0⟩ = some gsiAlg
  cpaCode_pin : Engine.P'.alg ⟨572, 0⟩ = some cpaCode
  cpaAlg_pin : Engine.P.alg ⟨572, 0⟩ = some cpaAlg
  pairCode_pin : Engine.P'.alg ⟨571, 0⟩ = some pairCode
  pairAlg_pin : Engine.P.alg ⟨571, 0⟩ = some pairAlg
  unitCode_pin : Engine.P'.alg ⟨2824, 0⟩ = some unitCode
  unitAlg_pin : Engine.P.alg ⟨2824, 0⟩ = some unitAlg
  leadCode_pin : Engine.P'.alg ⟨2825, 0⟩ = some leadCode
  leadAlg_pin : Engine.P.alg ⟨2825, 0⟩ = some leadAlg
  trailCode_pin : Engine.P'.alg ⟨2826, 0⟩ = some trailCode
  trailAlg_pin : Engine.P.alg ⟨2826, 0⟩ = some trailAlg
  cuCode_pin : Engine.P'.alg ⟨2823, 0⟩ = some cuCode
  cuAlg_pin : Engine.P.alg ⟨2823, 0⟩ = some cuAlg
  containsDfltCode_pin : Engine.P'.alg ⟨322, 0⟩ = some containsDfltCode
  containsDfltAlg_pin : Engine.P.alg ⟨322, 0⟩ = some containsDfltAlg
  containsPhCode_pin : Engine.P'.alg ⟨2725, 0⟩ = some containsPhCode
  containsPhAlg_pin : Engine.P.alg ⟨2725, 0⟩ = some containsPhAlg
  containsResCode_pin : Engine.P'.alg ⟨2562, 0⟩ = some containsResCode
  containsResAlg_pin : Engine.P.alg ⟨2562, 0⟩ = some containsResAlg
  containsTermCode_pin : Engine.P'.alg ⟨2728, 0⟩ = some containsTermCode
  containsTermAlg_pin : Engine.P.alg ⟨2728, 0⟩ = some containsTermAlg
  toStringCode_pin : Engine.P'.alg ⟨117, 0⟩ = some toStringCode
  toStringAlg_pin : Engine.P.alg ⟨117, 0⟩ = some toStringAlg
  tsReprCode_pin : Engine.P'.alg ⟨2633, 0⟩ = some tsReprCode
  tsReprAlg_pin : Engine.P.alg ⟨2633, 0⟩ = some tsReprAlg
  tsKDigitsCode_pin : Engine.P'.alg ⟨2637, 0⟩ = some tsKDigitsCode
  tsKDigitsAlg_pin : Engine.P.alg ⟨2637, 0⟩ = some tsKDigitsAlg
  tsUnitsCode_pin : Engine.P'.alg ⟨2641, 0⟩ = some tsUnitsCode
  tsUnitsAlg_pin : Engine.P.alg ⟨2641, 0⟩ = some tsUnitsAlg
  tsStrOfCode_pin : Engine.P'.alg ⟨2671, 0⟩ = some tsStrOfCode
  tsStrOfAlg_pin : Engine.P.alg ⟨2671, 0⟩ = some tsStrOfAlg
  tsOccCode_pin : Engine.P'.alg ⟨2700, 0⟩ = some tsOccCode
  tsOccAlg_pin : Engine.P.alg ⟨2700, 0⟩ = some tsOccAlg
  lsToStringCode_pin : Engine.P'.alg ⟨208, 0⟩ = some lsToStringCode
  lsToStringAlg_pin : Engine.P.alg ⟨208, 0⟩ = some lsToStringAlg
  lsHasPropertyCode_pin : Engine.P'.alg ⟨242, 0⟩ = some lsHasPropertyCode
  lsHasPropertyAlg_pin : Engine.P.alg ⟨242, 0⟩ = some lsHasPropertyAlg
  lsOrdHasCode_pin : Engine.P'.alg ⟨452, 0⟩ = some lsOrdHasCode
  lsOrdHasAlg_pin : Engine.P.alg ⟨452, 0⟩ = some lsOrdHasAlg
  lsOrdGopCode_pin : Engine.P'.alg ⟨446, 0⟩ = some lsOrdGopCode
  lsOrdGopAlg_pin : Engine.P.alg ⟨446, 0⟩ = some lsOrdGopAlg
  lsOrdGpoCode_pin : Engine.P'.alg ⟨438, 0⟩ = some lsOrdGpoCode
  lsOrdGpoAlg_pin : Engine.P.alg ⟨438, 0⟩ = some lsOrdGpoAlg
  lsOhpCode_pin : Engine.P'.alg ⟨453, 0⟩ = some lsOhpCode
  lsOhpAlg_pin : Engine.P.alg ⟨453, 0⟩ = some lsOhpAlg
  lsOgopCode_pin : Engine.P'.alg ⟨447, 0⟩ = some lsOgopCode
  lsOgopAlg_pin : Engine.P.alg ⟨447, 0⟩ = some lsOgopAlg
  lsOgpoCode_pin : Engine.P'.alg ⟨439, 0⟩ = some lsOgpoCode
  lsOgpoAlg_pin : Engine.P.alg ⟨439, 0⟩ = some lsOgpoAlg

export PinsHold (
  containsRows_true
  isWriteCode_pin isWriteAlg_pin
  stcpCode_pin stcpAlg_pin
  gsiCode_pin gsiAlg_pin
  cpaCode_pin cpaAlg_pin
  pairCode_pin pairAlg_pin
  unitCode_pin unitAlg_pin
  leadCode_pin leadAlg_pin
  trailCode_pin trailAlg_pin
  cuCode_pin cuAlg_pin
  containsDfltCode_pin containsDfltAlg_pin
  containsPhCode_pin containsPhAlg_pin
  containsResCode_pin containsResAlg_pin
  containsTermCode_pin containsTermAlg_pin
  toStringCode_pin toStringAlg_pin
  tsReprCode_pin tsReprAlg_pin
  tsKDigitsCode_pin tsKDigitsAlg_pin
  tsUnitsCode_pin tsUnitsAlg_pin
  tsStrOfCode_pin tsStrOfAlg_pin
  tsOccCode_pin tsOccAlg_pin
  lsToStringCode_pin lsToStringAlg_pin
  lsHasPropertyCode_pin lsHasPropertyAlg_pin
  lsOrdHasCode_pin lsOrdHasAlg_pin
  lsOrdGopCode_pin lsOrdGopAlg_pin
  lsOrdGpoCode_pin lsOrdGpoAlg_pin
  lsOhpCode_pin lsOhpAlg_pin
  lsOgopCode_pin lsOgopAlg_pin
  lsOgpoCode_pin lsOgpoAlg_pin
)

/-- Soundness of the runtime pin check: `pinsOk = true` yields all 55 pinned equations. -/
theorem pinsHold_of_ok (h : pinsOk = true) : PinsHold := by
  simp only [pinsOk, Bool.and_eq_true, and_assoc] at h
  rcases h with ⟨he, hcp, hco, hn, hr⟩
  simp only [exactPinsOk, Bool.and_eq_true, and_assoc] at he
  rcases he with ⟨h_iwC, h_iwA, h_stC, h_stA, h_gsC, h_gsA⟩
  simp only [cpPinsOk, Bool.and_eq_true, and_assoc] at hcp
  rcases hcp with ⟨h_cpaC, h_cpaA, h_prC, h_prA, h_unC, h_unA, h_ldC, h_ldA, h_trC, h_trA, h_cuC, h_cuA⟩
  simp only [containsPinsOk, Bool.and_eq_true, and_assoc] at hco
  rcases hco with ⟨h_cr, h_cdC, h_cdA, h_cpC, h_cpA, h_csC, h_csA, h_ctC, h_ctA⟩
  simp only [numIdxPinsOk, Bool.and_eq_true, and_assoc] at hn
  rcases hn with ⟨h_tsC, h_tsA, h_trpC, h_trpA, h_tkC, h_tkA, h_tuC, h_tuA, h_tsoC, h_tsoA, h_toC, h_toA⟩
  simp only [roundPinsOk, Bool.and_eq_true, and_assoc] at hr
  rcases hr with ⟨h_lstC, h_lstA, h_lhpC, h_lhpA, h_lohC, h_lohA, h_logpC, h_logpA, h_logoC, h_logoA,
    h_lphC, h_lphA, h_lggC, h_lggA, h_lgoC, h_lgoA⟩
  exact
    { containsRows_true := h_cr
      isWriteCode_pin := Engine.Pins.pin h_iwC
      isWriteAlg_pin := Engine.Pins.pin h_iwA
      stcpCode_pin := Engine.Pins.pin h_stC
      stcpAlg_pin := Engine.Pins.pin h_stA
      gsiCode_pin := Engine.Pins.pin h_gsC
      gsiAlg_pin := Engine.Pins.pin h_gsA
      cpaCode_pin := Engine.Pins.pin h_cpaC
      cpaAlg_pin := Engine.Pins.pin h_cpaA
      pairCode_pin := Engine.Pins.pin h_prC
      pairAlg_pin := Engine.Pins.pin h_prA
      unitCode_pin := Engine.Pins.pin h_unC
      unitAlg_pin := Engine.Pins.pin h_unA
      leadCode_pin := Engine.Pins.pin h_ldC
      leadAlg_pin := Engine.Pins.pin h_ldA
      trailCode_pin := Engine.Pins.pin h_trC
      trailAlg_pin := Engine.Pins.pin h_trA
      cuCode_pin := Engine.Pins.pin h_cuC
      cuAlg_pin := Engine.Pins.pin h_cuA
      containsDfltCode_pin := Engine.Pins.pin h_cdC
      containsDfltAlg_pin := Engine.Pins.pin h_cdA
      containsPhCode_pin := Engine.Pins.pin h_cpC
      containsPhAlg_pin := Engine.Pins.pin h_cpA
      containsResCode_pin := Engine.Pins.pin h_csC
      containsResAlg_pin := Engine.Pins.pin h_csA
      containsTermCode_pin := Engine.Pins.pin h_ctC
      containsTermAlg_pin := Engine.Pins.pin h_ctA
      toStringCode_pin := Engine.Pins.pin h_tsC
      toStringAlg_pin := Engine.Pins.pin h_tsA
      tsReprCode_pin := Engine.Pins.pin h_trpC
      tsReprAlg_pin := Engine.Pins.pin h_trpA
      tsKDigitsCode_pin := Engine.Pins.pin h_tkC
      tsKDigitsAlg_pin := Engine.Pins.pin h_tkA
      tsUnitsCode_pin := Engine.Pins.pin h_tuC
      tsUnitsAlg_pin := Engine.Pins.pin h_tuA
      tsStrOfCode_pin := Engine.Pins.pin h_tsoC
      tsStrOfAlg_pin := Engine.Pins.pin h_tsoA
      tsOccCode_pin := Engine.Pins.pin h_toC
      tsOccAlg_pin := Engine.Pins.pin h_toA
      lsToStringCode_pin := Engine.Pins.pin h_lstC
      lsToStringAlg_pin := Engine.Pins.pin h_lstA
      lsHasPropertyCode_pin := Engine.Pins.pin h_lhpC
      lsHasPropertyAlg_pin := Engine.Pins.pin h_lhpA
      lsOrdHasCode_pin := Engine.Pins.pin h_lohC
      lsOrdHasAlg_pin := Engine.Pins.pin h_lohA
      lsOrdGopCode_pin := Engine.Pins.pin h_logpC
      lsOrdGopAlg_pin := Engine.Pins.pin h_logpA
      lsOrdGpoCode_pin := Engine.Pins.pin h_logoC
      lsOrdGpoAlg_pin := Engine.Pins.pin h_logoA
      lsOhpCode_pin := Engine.Pins.pin h_lphC
      lsOhpAlg_pin := Engine.Pins.pin h_lphA
      lsOgopCode_pin := Engine.Pins.pin h_lggC
      lsOgopAlg_pin := Engine.Pins.pin h_lggA
      lsOgpoCode_pin := Engine.Pins.pin h_lgoC
      lsOgpoAlg_pin := Engine.Pins.pin h_lgoA }

end Engine.Machine

namespace Engine

open Ecma

/-- The engine's set-up at the host `H`: the accelerator table's shortcuts (`Machine.ctx`) when `accel` holds and
every pinned equation checks (`Machine.pinsOkThunk`), else none (`Machine.plain`), and the store's ceiling `mc`, in
cells. -/
def setupAt (H : Host Impl) (mc : Option Nat) (accel : Bool) (rd : ErratumId → Reading) (chk : Bool) :
    Machine.Setup :=
  let E := { Machine.ctx P' H rd chk with maxCells := mc }
  if accel && Machine.pinsOkThunk.get then E else Machine.plain E

end Engine
