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
    ((Op.call (CallK.alg { clause := Known.cPhContains, idx := 0 }) [Op.child 5 k, Op.bnd 0]).bind
      (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.val ValLit.true)]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [2], Ins.ret (Op.const (Const.val ValLit.false))]

/-- `Return the result of ComputedPropertyContains of child with argument symbol.` -/
def containsCpc1Code (k : NtId) : Code :=
  [Ins.site [1],
   Ins.ret (Op.call (CallK.alg { clause := Known.cPhResultOf, idx := 0 })
    [Op.on (OnK.sdo Known.sdoComputedPropertyContains) (Op.child 5 k) [Op.var 0]])]

/-- `Return the result of child Contains symbol.` (ComputedPropertyContains of a computed name). -/
def containsCpcPhCode (k : NtId) : Code :=
  [Ins.site [1],
   Ins.ret
    (Op.call (CallK.alg { clause := Known.cPhResultOf, idx := 0 })
      [Op.call (CallK.alg { clause := Known.cPhContains, idx := 0 }) [Op.child 5 k, Op.bnd 0]])]

/-- ComputedPropertyContains of two children in turn. -/
def containsCpc2Code (k1 k2 : NtId) : Code :=
  [Ins.site [1], Ins.let_ 1 (Op.on (OnK.sdo Known.sdoComputedPropertyContains) (Op.child 5 k1) [Op.var 0]), Ins.site [2],
   Ins.br ((Op.var 1).bind (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.val ValLit.true)]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [3],
   Ins.ret (Op.call (CallK.alg { clause := Known.cPhResultOf, idx := 0 })
    [Op.on (OnK.sdo Known.sdoComputedPropertyContains) (Op.child 5 k2) [Op.var 0]])]

/-- `If symbol is |K|, return true. Return ComputedPropertyContains of |K| with argument symbol.` -/
def containsIsSymCode (k : NtId) : Code :=
  [.site [1],
   .br ((Op.var 0).bind (.and [.leaf (.isVal false false) [.bound, .const (.nt k [])]]))
     [.ret (.const (.val .true))] [],
   .site [2],
   .ret (.call (.alg ⟨Known.cPhResultOf, 0⟩) [.on (.sdo Known.sdoComputedPropertyContains) (.child 5 k) [.var 0]])]

/-- `If symbol is the |ReservedWord| super, return true. Return false.` -/
def containsSuperCode : Code :=
  [Ins.site [1],
   Ins.br
    ((Op.var 0).bind
      (Op.and
        [Op.leaf (Leaf.isVal false false)
            [Op.bound,
              Op.call (CallK.alg { clause := Known.cPhTokenNt, idx := 0 })
                [Op.const (Const.nt Known.ntReservedWord []), Op.const (Const.term "super")]]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [2], Ins.ret (Op.const (Const.val ValLit.false))]

/-- An arrow function's parameters and body. -/
def containsArrow2Code : Code :=
  [Ins.site [1],
   Ins.br
    ((Op.var 0).bind
      (Op.and
        [Op.leaf (Leaf.isVal true false)
            [Op.bound, Op.const (Const.nt Known.ntNewTarget []), Op.const (Const.nt Known.ntSuperProperty []),
              Op.const (Const.nt Known.ntSuperCall []), Op.const (Const.term "super"), Op.const (Const.term "this")]]))
    [Ins.ret (Op.const (Const.val ValLit.false))] [],
   Ins.site [2],
   Ins.br
    ((Op.call (CallK.alg { clause := Known.cPhContains, idx := 0 }) [Op.child 5 Known.ntArrowParameters, Op.bnd 0]).bind
      (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.val ValLit.true)]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [3], Ins.ret (Op.call (CallK.alg { clause := Known.cPhContains, idx := 0 }) [Op.child 5 Known.ntConciseBody, Op.bnd 0])]

/-- An arrow function's body. -/
def containsArrow1Code : Code :=
  [Ins.site [1],
   Ins.br
    ((Op.var 0).bind
      (Op.and
        [Op.leaf (Leaf.isVal true false)
            [Op.bound, Op.const (Const.nt Known.ntNewTarget []), Op.const (Const.nt Known.ntSuperProperty []),
              Op.const (Const.nt Known.ntSuperCall []), Op.const (Const.term "super"), Op.const (Const.term "this")]]))
    [Ins.ret (Op.const (Const.val ValLit.false))] [],
   Ins.site [2], Ins.ret (Op.call (CallK.alg { clause := Known.cPhContains, idx := 0 }) [Op.child 5 Known.ntAsyncConciseBody, Op.bnd 0])]

/-- An async arrow function's head, a cover: only the symbol's test is the walk's. -/
def containsArrowDeclCode : Code :=
  [Ins.site [1],
   Ins.br
    ((Op.var 0).bind
      (Op.and
        [Op.leaf (Leaf.isVal true false)
            [Op.bound, Op.const (Const.nt Known.ntNewTarget []), Op.const (Const.nt Known.ntSuperProperty []),
              Op.const (Const.nt Known.ntSuperCall []), Op.const (Const.term "super"), Op.const (Const.term "this")]]))
    [Ins.ret (Op.const (Const.val ValLit.false))] [],
   Ins.site [2], Ins.let_ 1 (Op.call (CallK.prim Known.pCoveredBy) [Op.const (Const.nt Known.ntAsyncArrowHead []), Op.child 5 Known.ntCoverCallExpressionAndAsyncArrowHead]), Ins.site [3],
   Ins.br
    ((Op.call (CallK.alg { clause := Known.cPhContains, idx := 0 }) [Op.bnd 1, Op.bnd 0]).bind
      (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.val ValLit.true)]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [4], Ins.ret (Op.call (CallK.alg { clause := Known.cPhContains, idx := 0 }) [Op.child 5 Known.ntAsyncConciseBody, Op.bnd 0])]

def containsClassTailCode : Code :=
  [Ins.site [1],
   Ins.br ((Op.var 0).bind (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.nt Known.ntClassBody [])]]))
    [Ins.ret (Op.const (Const.val ValLit.true))] [],
   Ins.site [2],
   Ins.br ((Op.var 0).bind (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.nt Known.ntClassHeritage [])]]))
    [Ins.site [1, 2],
      Ins.br ((Op.child 5 Known.ntClassHeritage).bind (Op.and [Op.leaf (Leaf.isTy false false) [Op.call (CallK.prim Known.pPresent) [Op.bound]]]))
        [Ins.ret (Op.const (Const.val ValLit.true))] [],
      Ins.site [2, 2], Ins.ret (Op.const (Const.val ValLit.false))]
    [],
   Ins.site [3],
   Ins.br ((Op.child 5 Known.ntClassHeritage).bind (Op.and [Op.leaf (Leaf.isTy false false) [Op.call (CallK.prim Known.pPresent) [Op.bound]]]))
    [Ins.site [1, 3],
      Ins.br
        ((Op.call (CallK.alg { clause := Known.cPhContains, idx := 0 }) [Op.child 5 Known.ntClassHeritage, Op.bnd 0]).bind
          (Op.and [Op.leaf (Leaf.isVal false false) [Op.bound, Op.const (Const.val ValLit.true)]]))
        [Ins.ret (Op.const (Const.val ValLit.true))] []]
    [],
   Ins.site [4],
   Ins.ret (Op.call (CallK.alg { clause := Known.cPhResultOf, idx := 0 }) [Op.on (OnK.sdo Known.sdoComputedPropertyContains) (Op.child 5 Known.ntClassBody) [Op.var 0]])]

/-- Each row of Contains and ComputedPropertyContains the walk does not decline at: its variables' count, its
code. -/
def containsShapes : List (AlgId × Nat × Code) :=
  [(⟨Known.cStaticContains, 1⟩, 1, containsRetCode),
   (⟨Known.cStaticContains, 2⟩, 1, containsClassTailCode),
   (⟨Known.cStaticContains, 3⟩, 1, containsRetCode),
   (⟨Known.cStaticContains, 4⟩, 1, containsArrow2Code),
   (⟨Known.cStaticContains, 6⟩, 1, containsArrow1Code),
   (⟨Known.cStaticContains, 7⟩, 2, containsArrowDeclCode),
   (⟨Known.cStaticContains, 8⟩, 1, containsIsSymCode Known.ntMethodDefinition),
   (⟨Known.cStaticContains, 9⟩, 1, containsRetCode),
   (⟨Known.cStaticContains, 10⟩, 1, containsAny1Code Known.ntMemberExpression),
   (⟨Known.cStaticContains, 11⟩, 1, containsSuperCode),
   (⟨Known.cStaticContains, 12⟩, 1, containsAny1Code Known.ntCallExpression),
   (⟨Known.cStaticContains, 13⟩, 1, containsRetCode),
   (⟨Known.cStaticContains, 14⟩, 1, containsAny1Code Known.ntOptionalChain),
   (⟨Known.cStaticComputedPropertyContains, 0⟩, 1, containsRetCode),
   (⟨Known.cStaticComputedPropertyContains, 1⟩, 1, containsCpcPhCode Known.ntComputedPropertyName),
   (⟨Known.cStaticComputedPropertyContains, 2⟩, 1, containsCpc1Code Known.ntClassElementName),
   (⟨Known.cStaticComputedPropertyContains, 3⟩, 1, containsCpc1Code Known.ntClassElementName),
   (⟨Known.cStaticComputedPropertyContains, 4⟩, 1, containsCpc1Code Known.ntClassElementName),
   (⟨Known.cStaticComputedPropertyContains, 5⟩, 2, containsCpc2Code Known.ntClassElementList Known.ntClassElement),
   (⟨Known.cStaticComputedPropertyContains, 6⟩, 1, containsRetCode),
   (⟨Known.cStaticComputedPropertyContains, 7⟩, 1, containsRetCode),
   (⟨Known.cStaticComputedPropertyContains, 8⟩, 1, containsCpc1Code Known.ntClassElementName),
   (⟨Known.cStaticComputedPropertyContains, 9⟩, 1, containsCpc1Code Known.ntClassElementName)]

/-- The check of the program's row table: at each key of Contains or ComputedPropertyContains whose row has an
id of `containsShapes`, the row has that many variables and the key's code is that code. -/
def containsRowsCheck : Bool :=
  Spec.src.rowMap.keys.all fun (s, k) => !(s == Known.sdoContains || s == Known.sdoComputedPropertyContains) ||
    (match Engine.P.row s k with
    | none => true
    | some r => match containsShapes.lookup r.id with
      | none => true
      | some (n, code) => r.vars.size == n && Code.optEqB (Engine.P'.row s k) (some code))

/-! ## StringNumericValue and MV row shapes and check -/

def snvStrNumLitCode : Code :=
  [Ins.site [1], Ins.ret (Op.on (OnK.sdo Known.sdoStringNumericValue) (Op.child 5 Known.ntStrNumericLiteral) [])]

def snvStrUnsignedDigitsCode : Code :=
  [Ins.site [1], Ins.let_ 0 (Op.on (OnK.sdo Known.sdoMV) (Op.child 5 Known.ntDecimalDigits) []), Ins.site [2],
   Ins.br ((Op.child 5 Known.ntExponentPart).bind (Op.and [Op.leaf (Leaf.isTy false false) [Op.call (CallK.prim Known.pPresent) [Op.bound]]]))
     [Ins.let_ 1 (Op.on (OnK.sdo Known.sdoMV) (Op.child 5 Known.ntExponentPart) [])]
     [Ins.let_ 1 (Op.const (Const.math Sign.none (Mag.num (Numeral.dec 0))))],
   Ins.site [3], Ins.ret (Op.call (CallK.alg ⟨Known.cFormalRoundDecimalMV, 0⟩) [Op.var 0, Op.var 1])]

def mvDecDigitsStepCode : Code :=
  [Ins.site [1],
   Ins.ret (Op.leaf (Leaf.bin BinOp.add)
     [Op.leaf (Leaf.bin BinOp.mul)
        [Op.on (OnK.sdo Known.sdoMV) (Op.child 5 Known.ntDecimalDigits) [],
         Op.const (Const.math Sign.none (Mag.num (Numeral.dec 10)))],
      Op.on (OnK.sdo Known.sdoMV) (Op.child 5 Known.ntDecimalDigit) []])]

def mvDecDigitCode (d : Nat) : Code :=
  [Ins.site [1], Ins.ret (Op.const (Const.math Sign.none (Mag.num (Numeral.dec d))))]

def decDigitProds : List (ProdId × Nat) :=
  [(Known.prodDecDigit0, 0), (Known.prodDecDigit1, 1), (Known.prodDecDigit2, 2), (Known.prodDecDigit3, 3),
   (Known.prodDecDigit4, 4), (Known.prodDecDigit5, 5), (Known.prodDecDigit6, 6), (Known.prodDecDigit7, 7),
   (Known.prodDecDigit8, 8), (Known.prodDecDigit9, 9)]

def snvRowHas (s : SdoId) (k : ProdId) (n : Nat) (code : Code) : Bool :=
  match Engine.P.row s k with
  | some r => r.vars.size == n && Code.optEqB (Engine.P'.row s k) (some code)
  | none => false

def snvChainHas (s : SdoId) (k : ProdId) (ch : NtId) : Bool :=
  (Engine.P.row s k).isNone && Engine.P.chain k == some ch

def snvRowsCheck : Bool :=
  Engine.P.sdoArity Known.sdoStringNumericValue == 0 &&
  !Engine.P.sdoRc Known.sdoStringNumericValue &&
  (Engine.P.sdoDefault Known.sdoStringNumericValue).isNone &&
  Engine.P.sdoArity Known.sdoMV == 0 &&
  !Engine.P.sdoRc Known.sdoMV &&
  (Engine.P.sdoDefault Known.sdoMV).isNone &&
  snvRowHas Known.sdoStringNumericValue Known.prodStrNumLit 0 snvStrNumLitCode &&
  snvChainHas Known.sdoStringNumericValue Known.prodStrNumDec Known.ntStrDecimalLiteral &&
  snvChainHas Known.sdoStringNumericValue Known.prodStrDecUnsigned Known.ntStrUnsignedDecimalLiteral &&
  snvRowHas Known.sdoStringNumericValue Known.prodStrUnsignedDigits 2 snvStrUnsignedDigitsCode &&
  snvChainHas Known.sdoMV Known.prodDecDigits1 Known.ntDecimalDigit &&
  snvRowHas Known.sdoMV Known.prodDecDigitsStep 0 mvDecDigitsStepCode &&
  decDigitProds.all fun (p, d) => snvRowHas Known.sdoMV p 0 (mvDecDigitCode d)

/-! ## Pinned specification units and Boolean tests -/

-- Exact algorithm rows (20)
pin_alg_def isWriteCode ⟨Known.cSortWriteSharedMemoryEvent, 0⟩
pin_prog_alg_def isWriteAlg ⟨Known.cSortWriteSharedMemoryEvent, 0⟩
pin_alg_def stcpCode ⟨Known.cStringToCodePoints, 0⟩
pin_prog_alg_def stcpAlg ⟨Known.cStringToCodePoints, 0⟩
pin_alg_def gsiCode ⟨Known.cGetStringIndex, 0⟩
pin_prog_alg_def gsiAlg ⟨Known.cGetStringIndex, 0⟩
pin_alg_def utf16EncCode ⟨Known.cUTF16EncodeCodePoint, 0⟩
pin_prog_alg_def utf16EncAlg ⟨Known.cUTF16EncodeCodePoint, 0⟩
pin_alg_def cptsCode ⟨Known.cCodePointsToString, 0⟩
pin_prog_alg_def cptsAlg ⟨Known.cCodePointsToString, 0⟩
pin_alg_def toNumCode ⟨Known.cToNumber, 0⟩
pin_prog_alg_def toNumAlg ⟨Known.cToNumber, 0⟩
pin_alg_def cnisCode ⟨Known.cCanonicalNumericIndexString, 0⟩
pin_prog_alg_def cnisAlg ⟨Known.cCanonicalNumericIndexString, 0⟩
pin_alg_def roundDecMVCode ⟨Known.cFormalRoundDecimalMV, 0⟩
pin_prog_alg_def roundDecMVAlg ⟨Known.cFormalRoundDecimalMV, 0⟩
pin_alg_def roundMVResCode ⟨Known.cRoundMVResult, 0⟩
pin_prog_alg_def roundMVResAlg ⟨Known.cRoundMVResult, 0⟩
pin_alg_def ph20DigitsCode ⟨Known.cPhTwentySignificantDigits, 0⟩
pin_prog_alg_def ph20DigitsAlg ⟨Known.cPhTwentySignificantDigits, 0⟩

-- CodePointAt and surrogate/code-unit sorts (12)
pin_alg_def cpaCode ⟨Known.cCodePointAt, 0⟩
pin_prog_alg_def cpaAlg ⟨Known.cCodePointAt, 0⟩
pin_alg_def pairCode ⟨Known.cUTF16SurrogatePair, 0⟩
pin_prog_alg_def pairAlg ⟨Known.cUTF16SurrogatePair, 0⟩
pin_alg_def unitCode ⟨Known.cSortSurrogate, 0⟩
pin_prog_alg_def unitAlg ⟨Known.cSortSurrogate, 0⟩
pin_alg_def leadCode ⟨Known.cSortLeading, 0⟩
pin_prog_alg_def leadAlg ⟨Known.cSortLeading, 0⟩
pin_alg_def trailCode ⟨Known.cSortTrailing, 0⟩
pin_prog_alg_def trailAlg ⟨Known.cSortTrailing, 0⟩
pin_alg_def cuCode ⟨Known.cSortCodeUnit, 0⟩
pin_prog_alg_def cuAlg ⟨Known.cSortCodeUnit, 0⟩

-- Contains helpers (8 + containsRowsCheck)
pin_alg_def containsDfltCode ⟨Known.cStaticContains, 0⟩
pin_prog_alg_def containsDfltAlg ⟨Known.cStaticContains, 0⟩
pin_alg_def containsPhCode ⟨Known.cPhContains, 0⟩
pin_prog_alg_def containsPhAlg ⟨Known.cPhContains, 0⟩
pin_alg_def containsResCode ⟨Known.cPhResultOf, 0⟩
pin_prog_alg_def containsResAlg ⟨Known.cPhResultOf, 0⟩
pin_alg_def containsTermCode ⟨Known.cPhTokenNt, 0⟩
pin_prog_alg_def containsTermAlg ⟨Known.cPhTokenNt, 0⟩

-- Number::toString helpers (12)
pin_alg_def toStringCode ⟨Known.cNumberToString, 0⟩
pin_prog_alg_def toStringAlg ⟨Known.cNumberToString, 0⟩
pin_alg_def tsReprCode ⟨Known.cPhRepresentationRadix, 0⟩
pin_prog_alg_def tsReprAlg ⟨Known.cPhRepresentationRadix, 0⟩
pin_alg_def tsKDigitsCode ⟨Known.cPhKDigits, 0⟩
pin_prog_alg_def tsKDigitsAlg ⟨Known.cPhKDigits, 0⟩
pin_alg_def tsUnitsCode ⟨Known.cPhCodeUnitsOf, 0⟩
pin_prog_alg_def tsUnitsAlg ⟨Known.cPhCodeUnitsOf, 0⟩
pin_alg_def tsStrOfCode ⟨Known.cPhStringSolely, 0⟩
pin_prog_alg_def tsStrOfAlg ⟨Known.cPhStringSolely, 0⟩
pin_alg_def tsOccCode ⟨Known.cPhOccurrencesOf, 0⟩
pin_prog_alg_def tsOccAlg ⟨Known.cPhOccurrencesOf, 0⟩

-- LoopSkip algorithms (16)
pin_alg_def lsToStringCode ⟨Known.cToString, 0⟩
pin_prog_alg_def lsToStringAlg ⟨Known.cToString, 0⟩
pin_alg_def lsHasPropertyCode ⟨Known.cHasProperty, 0⟩
pin_prog_alg_def lsHasPropertyAlg ⟨Known.cHasProperty, 0⟩
pin_alg_def lsOrdHasCode ⟨Known.cOrdMethodHasProperty, 0⟩
pin_prog_alg_def lsOrdHasAlg ⟨Known.cOrdMethodHasProperty, 0⟩
pin_alg_def lsOrdGopCode ⟨Known.cOrdMethodGetOwnProperty, 0⟩
pin_prog_alg_def lsOrdGopAlg ⟨Known.cOrdMethodGetOwnProperty, 0⟩
pin_alg_def lsOrdGpoCode ⟨Known.cOrdMethodGetPrototypeOf, 0⟩
pin_prog_alg_def lsOrdGpoAlg ⟨Known.cOrdMethodGetPrototypeOf, 0⟩
pin_alg_def lsOhpCode ⟨Known.cOrdinaryHasProperty, 0⟩
pin_prog_alg_def lsOhpAlg ⟨Known.cOrdinaryHasProperty, 0⟩
pin_alg_def lsOgopCode ⟨Known.cOrdinaryGetOwnProperty, 0⟩
pin_prog_alg_def lsOgopAlg ⟨Known.cOrdinaryGetOwnProperty, 0⟩
pin_alg_def lsOgpoCode ⟨Known.cOrdinaryGetPrototypeOf, 0⟩
pin_prog_alg_def lsOgpoAlg ⟨Known.cOrdinaryGetPrototypeOf, 0⟩

/-- Named list of all 70 pin checks (`ecma-run --check-pins`). -/
def pinChecks : List (String × (Unit → Bool)) :=
  [("containsRows", fun _ => containsRowsCheck),
   ("snvRows", fun _ => snvRowsCheck),
   ("isWriteCode", fun _ => isWriteCode_ok),
   ("isWriteAlg", fun _ => isWriteAlg_ok),
   ("stcpCode", fun _ => stcpCode_ok),
   ("stcpAlg", fun _ => stcpAlg_ok),
   ("gsiCode", fun _ => gsiCode_ok),
   ("gsiAlg", fun _ => gsiAlg_ok),
   ("utf16EncCode", fun _ => utf16EncCode_ok),
   ("utf16EncAlg", fun _ => utf16EncAlg_ok),
   ("cptsCode", fun _ => cptsCode_ok),
   ("cptsAlg", fun _ => cptsAlg_ok),
   ("toNumCode", fun _ => toNumCode_ok),
   ("toNumAlg", fun _ => toNumAlg_ok),
   ("cnisCode", fun _ => cnisCode_ok),
   ("cnisAlg", fun _ => cnisAlg_ok),
   ("roundDecMVCode", fun _ => roundDecMVCode_ok),
   ("roundDecMVAlg", fun _ => roundDecMVAlg_ok),
   ("roundMVResCode", fun _ => roundMVResCode_ok),
   ("roundMVResAlg", fun _ => roundMVResAlg_ok),
   ("ph20DigitsCode", fun _ => ph20DigitsCode_ok),
   ("ph20DigitsAlg", fun _ => ph20DigitsAlg_ok),
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
   ("lsOgpoAlg", fun _ => lsOgpoAlg_ok),
   ("parseTables", Engine.Parse.checkParseTables)]

/-- Names of any failed pin checks. -/
def failedPins : List String :=
  pinChecks.filterMap fun (n, f) => if f () then none else some n

def exactPinsOk : Bool :=
  isWriteCode_ok && isWriteAlg_ok && stcpCode_ok && stcpAlg_ok && gsiCode_ok && gsiAlg_ok &&
  utf16EncCode_ok && utf16EncAlg_ok && cptsCode_ok && cptsAlg_ok &&
  toNumCode_ok && toNumAlg_ok && cnisCode_ok && cnisAlg_ok &&
  roundDecMVCode_ok && roundDecMVAlg_ok && roundMVResCode_ok && roundMVResAlg_ok &&
  ph20DigitsCode_ok && ph20DigitsAlg_ok && snvRowsCheck

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
  snvRows_true : snvRowsCheck = true
  isWriteCode_pin : Engine.P'.alg ⟨Known.cSortWriteSharedMemoryEvent, 0⟩ = some isWriteCode
  isWriteAlg_pin : Engine.P.alg ⟨Known.cSortWriteSharedMemoryEvent, 0⟩ = some isWriteAlg
  stcpCode_pin : Engine.P'.alg ⟨Known.cStringToCodePoints, 0⟩ = some stcpCode
  stcpAlg_pin : Engine.P.alg ⟨Known.cStringToCodePoints, 0⟩ = some stcpAlg
  gsiCode_pin : Engine.P'.alg ⟨Known.cGetStringIndex, 0⟩ = some gsiCode
  gsiAlg_pin : Engine.P.alg ⟨Known.cGetStringIndex, 0⟩ = some gsiAlg
  utf16EncCode_pin : Engine.P'.alg ⟨Known.cUTF16EncodeCodePoint, 0⟩ = some utf16EncCode
  utf16EncAlg_pin : Engine.P.alg ⟨Known.cUTF16EncodeCodePoint, 0⟩ = some utf16EncAlg
  cptsCode_pin : Engine.P'.alg ⟨Known.cCodePointsToString, 0⟩ = some cptsCode
  cptsAlg_pin : Engine.P.alg ⟨Known.cCodePointsToString, 0⟩ = some cptsAlg
  toNumCode_pin : Engine.P'.alg ⟨Known.cToNumber, 0⟩ = some toNumCode
  toNumAlg_pin : Engine.P.alg ⟨Known.cToNumber, 0⟩ = some toNumAlg
  cnisCode_pin : Engine.P'.alg ⟨Known.cCanonicalNumericIndexString, 0⟩ = some cnisCode
  cnisAlg_pin : Engine.P.alg ⟨Known.cCanonicalNumericIndexString, 0⟩ = some cnisAlg
  roundDecMVCode_pin : Engine.P'.alg ⟨Known.cFormalRoundDecimalMV, 0⟩ = some roundDecMVCode
  roundDecMVAlg_pin : Engine.P.alg ⟨Known.cFormalRoundDecimalMV, 0⟩ = some roundDecMVAlg
  roundMVResCode_pin : Engine.P'.alg ⟨Known.cRoundMVResult, 0⟩ = some roundMVResCode
  roundMVResAlg_pin : Engine.P.alg ⟨Known.cRoundMVResult, 0⟩ = some roundMVResAlg
  ph20DigitsCode_pin : Engine.P'.alg ⟨Known.cPhTwentySignificantDigits, 0⟩ = some ph20DigitsCode
  ph20DigitsAlg_pin : Engine.P.alg ⟨Known.cPhTwentySignificantDigits, 0⟩ = some ph20DigitsAlg
  cpaCode_pin : Engine.P'.alg ⟨Known.cCodePointAt, 0⟩ = some cpaCode
  cpaAlg_pin : Engine.P.alg ⟨Known.cCodePointAt, 0⟩ = some cpaAlg
  pairCode_pin : Engine.P'.alg ⟨Known.cUTF16SurrogatePair, 0⟩ = some pairCode
  pairAlg_pin : Engine.P.alg ⟨Known.cUTF16SurrogatePair, 0⟩ = some pairAlg
  unitCode_pin : Engine.P'.alg ⟨Known.cSortSurrogate, 0⟩ = some unitCode
  unitAlg_pin : Engine.P.alg ⟨Known.cSortSurrogate, 0⟩ = some unitAlg
  leadCode_pin : Engine.P'.alg ⟨Known.cSortLeading, 0⟩ = some leadCode
  leadAlg_pin : Engine.P.alg ⟨Known.cSortLeading, 0⟩ = some leadAlg
  trailCode_pin : Engine.P'.alg ⟨Known.cSortTrailing, 0⟩ = some trailCode
  trailAlg_pin : Engine.P.alg ⟨Known.cSortTrailing, 0⟩ = some trailAlg
  cuCode_pin : Engine.P'.alg ⟨Known.cSortCodeUnit, 0⟩ = some cuCode
  cuAlg_pin : Engine.P.alg ⟨Known.cSortCodeUnit, 0⟩ = some cuAlg
  containsDfltCode_pin : Engine.P'.alg ⟨Known.cStaticContains, 0⟩ = some containsDfltCode
  containsDfltAlg_pin : Engine.P.alg ⟨Known.cStaticContains, 0⟩ = some containsDfltAlg
  containsPhCode_pin : Engine.P'.alg ⟨Known.cPhContains, 0⟩ = some containsPhCode
  containsPhAlg_pin : Engine.P.alg ⟨Known.cPhContains, 0⟩ = some containsPhAlg
  containsResCode_pin : Engine.P'.alg ⟨Known.cPhResultOf, 0⟩ = some containsResCode
  containsResAlg_pin : Engine.P.alg ⟨Known.cPhResultOf, 0⟩ = some containsResAlg
  containsTermCode_pin : Engine.P'.alg ⟨Known.cPhTokenNt, 0⟩ = some containsTermCode
  containsTermAlg_pin : Engine.P.alg ⟨Known.cPhTokenNt, 0⟩ = some containsTermAlg
  toStringCode_pin : Engine.P'.alg ⟨Known.cNumberToString, 0⟩ = some toStringCode
  toStringAlg_pin : Engine.P.alg ⟨Known.cNumberToString, 0⟩ = some toStringAlg
  tsReprCode_pin : Engine.P'.alg ⟨Known.cPhRepresentationRadix, 0⟩ = some tsReprCode
  tsReprAlg_pin : Engine.P.alg ⟨Known.cPhRepresentationRadix, 0⟩ = some tsReprAlg
  tsKDigitsCode_pin : Engine.P'.alg ⟨Known.cPhKDigits, 0⟩ = some tsKDigitsCode
  tsKDigitsAlg_pin : Engine.P.alg ⟨Known.cPhKDigits, 0⟩ = some tsKDigitsAlg
  tsUnitsCode_pin : Engine.P'.alg ⟨Known.cPhCodeUnitsOf, 0⟩ = some tsUnitsCode
  tsUnitsAlg_pin : Engine.P.alg ⟨Known.cPhCodeUnitsOf, 0⟩ = some tsUnitsAlg
  tsStrOfCode_pin : Engine.P'.alg ⟨Known.cPhStringSolely, 0⟩ = some tsStrOfCode
  tsStrOfAlg_pin : Engine.P.alg ⟨Known.cPhStringSolely, 0⟩ = some tsStrOfAlg
  tsOccCode_pin : Engine.P'.alg ⟨Known.cPhOccurrencesOf, 0⟩ = some tsOccCode
  tsOccAlg_pin : Engine.P.alg ⟨Known.cPhOccurrencesOf, 0⟩ = some tsOccAlg
  lsToStringCode_pin : Engine.P'.alg ⟨Known.cToString, 0⟩ = some lsToStringCode
  lsToStringAlg_pin : Engine.P.alg ⟨Known.cToString, 0⟩ = some lsToStringAlg
  lsHasPropertyCode_pin : Engine.P'.alg ⟨Known.cHasProperty, 0⟩ = some lsHasPropertyCode
  lsHasPropertyAlg_pin : Engine.P.alg ⟨Known.cHasProperty, 0⟩ = some lsHasPropertyAlg
  lsOrdHasCode_pin : Engine.P'.alg ⟨Known.cOrdMethodHasProperty, 0⟩ = some lsOrdHasCode
  lsOrdHasAlg_pin : Engine.P.alg ⟨Known.cOrdMethodHasProperty, 0⟩ = some lsOrdHasAlg
  lsOrdGopCode_pin : Engine.P'.alg ⟨Known.cOrdMethodGetOwnProperty, 0⟩ = some lsOrdGopCode
  lsOrdGopAlg_pin : Engine.P.alg ⟨Known.cOrdMethodGetOwnProperty, 0⟩ = some lsOrdGopAlg
  lsOrdGpoCode_pin : Engine.P'.alg ⟨Known.cOrdMethodGetPrototypeOf, 0⟩ = some lsOrdGpoCode
  lsOrdGpoAlg_pin : Engine.P.alg ⟨Known.cOrdMethodGetPrototypeOf, 0⟩ = some lsOrdGpoAlg
  lsOhpCode_pin : Engine.P'.alg ⟨Known.cOrdinaryHasProperty, 0⟩ = some lsOhpCode
  lsOhpAlg_pin : Engine.P.alg ⟨Known.cOrdinaryHasProperty, 0⟩ = some lsOhpAlg
  lsOgopCode_pin : Engine.P'.alg ⟨Known.cOrdinaryGetOwnProperty, 0⟩ = some lsOgopCode
  lsOgopAlg_pin : Engine.P.alg ⟨Known.cOrdinaryGetOwnProperty, 0⟩ = some lsOgopAlg
  lsOgpoCode_pin : Engine.P'.alg ⟨Known.cOrdinaryGetPrototypeOf, 0⟩ = some lsOgpoCode
  lsOgpoAlg_pin : Engine.P.alg ⟨Known.cOrdinaryGetPrototypeOf, 0⟩ = some lsOgpoAlg

export PinsHold (
  containsRows_true snvRows_true
  isWriteCode_pin isWriteAlg_pin
  stcpCode_pin stcpAlg_pin
  gsiCode_pin gsiAlg_pin
  utf16EncCode_pin utf16EncAlg_pin
  cptsCode_pin cptsAlg_pin
  toNumCode_pin toNumAlg_pin
  cnisCode_pin cnisAlg_pin
  roundDecMVCode_pin roundDecMVAlg_pin
  roundMVResCode_pin roundMVResAlg_pin
  ph20DigitsCode_pin ph20DigitsAlg_pin
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
  rcases he with ⟨h_iwC, h_iwA, h_stC, h_stA, h_gsC, h_gsA,
    h_u16C, h_u16A, h_cptsC, h_cptsA, h_tnC, h_tnA, h_cnC, h_cnA,
    h_rdC, h_rdA, h_rmC, h_rmA, h_p20C, h_p20A, h_snvR⟩
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
      snvRows_true := h_snvR
      isWriteCode_pin := Engine.Pins.pin h_iwC
      isWriteAlg_pin := Engine.Pins.pin h_iwA
      stcpCode_pin := Engine.Pins.pin h_stC
      stcpAlg_pin := Engine.Pins.pin h_stA
      gsiCode_pin := Engine.Pins.pin h_gsC
      gsiAlg_pin := Engine.Pins.pin h_gsA
      utf16EncCode_pin := Engine.Pins.pin h_u16C
      utf16EncAlg_pin := Engine.Pins.pin h_u16A
      cptsCode_pin := Engine.Pins.pin h_cptsC
      cptsAlg_pin := Engine.Pins.pin h_cptsA
      toNumCode_pin := Engine.Pins.pin h_tnC
      toNumAlg_pin := Engine.Pins.pin h_tnA
      cnisCode_pin := Engine.Pins.pin h_cnC
      cnisAlg_pin := Engine.Pins.pin h_cnA
      roundDecMVCode_pin := Engine.Pins.pin h_rdC
      roundDecMVAlg_pin := Engine.Pins.pin h_rdA
      roundMVResCode_pin := Engine.Pins.pin h_rmC
      roundMVResAlg_pin := Engine.Pins.pin h_rmA
      ph20DigitsCode_pin := Engine.Pins.pin h_p20C
      ph20DigitsAlg_pin := Engine.Pins.pin h_p20A
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
def setupAt (H : Host Impl) (mc : Option Nat) (accel : Bool) (chk : Bool) :
    Machine.Setup :=
  let E := { Machine.ctx P' H chk with maxCells := mc }
  if accel && Machine.pinsOkThunk.get then E else Machine.plain E

end Engine
