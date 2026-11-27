module

public import Engine.Model.NumericString
public import Engine.Model.Parent
public import Engine.Parse.Parse
public import Engine.Parse.Shape
public import Ecma.Model.NodeRel
public import Engine.Model.JsonText

@[expose] public section

/-!
# Accelerator: ParseText's parse at Impl

`parse` is `Model.parse` at Impl. Valid StringNumericLiteral and StringIntegerLiteral inputs use
the linear numeric-string fast path (`parseNumeric`, verified directly against GL via
`verifyCodeNode`); rejected numeric inputs and all other goals go to `Parse` with Bare's Parse
Nodes as its nodes. At |JSONText|, an input ECMA-404's recognizer (`Engine.JsonText.text`) rejects
is "no parse" without `Parse`; so is a |StringLiteral| input whose first code point is neither `"`
nor `'` (`firstSet`).

The code point classes (`<USP>`, ID_Start, ID_Continue) are `Engine.Model.codePrims`.
-/

namespace Engine

open Engine.Model Ecma.Grammar
open Ecma (ProdId NtId ParamId ParseCx)

/-- Bare's Parse Nodes as Parse's, with Bare's code point classes. -/
def builder : Engine.Parse.Builder Node where
  node stamp lo hi p nt ps kids text := .mk stamp lo hi p nt ps kids text
  prod | .mk _ _ _ p _ _ _ _ => p
  nt | .mk _ _ _ _ n _ _ _ => n
  args | .mk _ _ _ _ _ ps _ _ => ps
  span | .mk _ i j _ _ _ _ _ => (i, j)
  kids | .mk _ _ _ _ _ _ ks _ => ks
  stamp | .mk k _ _ _ _ _ _ _ => k
  text | .mk _ _ _ _ _ _ _ t => t.toArray
  usp := usp
  idStart := idStart
  idContinue := idContinue

/-- The code points of a parse's input; none if one is not a Unicode code point (`0 .. 0x10FFFF`). -/
def codePointsOf (src : Array MathVal) : Option (Array Nat) :=
  src.mapM fun | .int i => if 0 ≤ i ∧ i ≤ 0x10FFFF then some i.toNat else none | _ => none

/-- The goal is |JSONText| and `cs` is not a JSON text: no derivation. -/
def noJSON (goal : NtId) (cs : Array Nat) : Bool :=
  goal == NT.JSONText.ctorIdx && !Engine.JsonText.text ⟨(· == ·), (· < ·)⟩ cs.toList

/-- The code points a lexical goal's derivations start with, where checked: |StringLiteral|'s `"` and `'`. -/
def firstSet (goal : NtId) : Option (List Nat) :=
  if goal == NT.StringLiteral.ctorIdx then some [34, 39] else none

/-- `cs` starts with a code point outside the goal's `firstSet`: no derivation. -/
def noFirst (goal : NtId) (cs : Array Nat) : Bool :=
  match firstSet goal, cs[0]? with
  | some fs, some c => !fs.contains c
  | _, _ => false

/-- The children `i` on of `kids` are the occurrences `os`, in order. -/
def slotsOk (kids : Array (NtId × Option Node)) : List (NT × Bool) → Nat → Bool
  | [], i => i == kids.size
  | (n, b) :: os, i => match kids[i]? with
    | some (t, some (.mk _ _ _ _ m _ _ _)) => b && t == n.ctorIdx && m == n.ctorIdx && slotsOk kids os (i + 1)
    | some (t, none) => !b && t == n.ctorIdx && slotsOk kids os (i + 1)
    | none => false

/-- At every node of the tree `n`, the children are the occurrences of the node's production (`occs`, by
production id) with their presences (`slotsOk`): what `Model.NodeLaws.child_parse` says of a parse. -/
def shapeOk (occs : Nat → List (NT × Bool)) : Node → Bool
  | .mk _ _ _ p _ _ kids _ => slotsOk kids (occs p) 0 && kids.attach.all fun ⟨c, h⟩ => c.2.attach.all fun ⟨x, hx⟩ =>
      have : sizeOf x < sizeOf c := by
        rcases c with ⟨a, _ | y⟩ <;> simp at hx; subst hx; simp; omega
      have := Array.sizeOf_lt_of_mem h
      shapeOk occs x

/-- The check of a parse: every node's children are its production's occurrences. -/
def shaped : Node → Bool := shapeOk Engine.Parse.occsBy

/-- Pure verifier building a positive `Grammar.Tree` derivation witness for a code-point `Node`
(used to validate `parseNumeric`'s linear fast path). -/
def verifyCodeNode (cs : Array Nat) (cx : Ctx) (g : GrammarId) (st : Nat) : Nat → Node → Option Tree
  | 0, _ => none
  | fuel + 1, .mk st' lo hi pid nt ps kids txt => do
    guard (st' == st && lo ≤ hi && hi ≤ cs.size && txt.toArray == cs.extract lo hi)
    let P ← Engine.Parse.prodOf pid
    guard (P.rule.lhs.ctorIdx == nt)
    let s ← (Engine.Parse.altsOf cx g P.rule.lhs).find? fun e =>
      e.grammar == P.grammar && e.idx == P.alt && e.rule == P.rule
    guard (s.alt.guard.all (Guard.holds ps) && Engine.Parse.prodIdOf s P.mask == some pid)
    let (endPos, ts) ← verifyItems fuel ps s.alt.rhs P.mask kids.toList lo
    guard (endPos == hi)
    return .node P.rule.lhs pid ps lo hi ts
where
  verifyItems (fuel : Nat) (ps : List Param) :
      List Item → List Bool → List (NtId × Option Node) → Nat → Option (Nat × List Tree)
    | [], [], [], pos => some (pos, [])
    | .sym (.t _) true :: is, false :: ms, ks, pos => verifyItems fuel ps is ms ks pos
    | .sym (.nt m _) true :: is, false :: ms, (kt, none) :: ks, pos => do
      guard (kt == m.ctorIdx)
      verifyItems fuel ps is ms ks pos
    | .sym (.t x) false :: is, ms, ks, pos => do
      let j ← Engine.Parse.Code.termEnd builder cs x pos
      let (e, ts) ← verifyItems fuel ps is ms ks j
      return (e, .leaf pos j :: ts)
    | .sym (.t x) true :: is, true :: ms, ks, pos => do
      let j ← Engine.Parse.Code.termEnd builder cs x pos
      let (e, ts) ← verifyItems fuel ps is ms ks j
      return (e, .leaf pos j :: ts)
    | .sym (.nt m args) false :: is, ms, (kt, some c) :: ks, pos => do
      guard (kt == m.ctorIdx && builder.nt c == m.ctorIdx && noCondAfter is &&
        builder.args c == applyArgs ps args && (builder.span c).1 == pos)
      let tc ← verifyCodeNode cs cx g st fuel c
      let (e, ts) ← verifyItems fuel ps is ms ks (builder.span c).2
      return (e, tc :: ts)
    | .sym (.nt m args) true :: is, true :: ms, (kt, some c) :: ks, pos => do
      guard (kt == m.ctorIdx && builder.nt c == m.ctorIdx && noCondAfter is &&
        builder.args c == applyArgs ps args && (builder.span c).1 == pos)
      let tc ← verifyCodeNode cs cx g st fuel c
      let (e, ts) ← verifyItems fuel ps is ms ks (builder.span c).2
      return (e, tc :: ts)
    | .empty :: is, ms, ks, pos => verifyItems fuel ps is ms ks pos
    | _, _, _, _ => none

/-- An outcome whose Parse Node passes `ok`; a stop where it does not. -/
@[reducible] def checked (ok : Node → Bool) : Engine.Parse.Outcome Node → Engine.Parse.Outcome Node
  | .ok n => if ok n then .ok n else .stop (.check "a Parse Node whose children are not its production's")
  | o => o

/-- Parse's outcome for a goal at Bare, in context `cx`, `strict` its source text being strict mode
code from outside. -/
def outcome (stamp : Nat) (src : Array MathVal) (goal : NtId) (args : List (ParamId × Bool))
    (cx : Ctx := ⟨false, {}⟩) (strict : Bool := false) :
    Engine.Parse.Outcome Node :=
  match codePointsOf src with
  | some cs =>
    if noFirst goal cs || noJSON goal cs then .noParse
    else checked shaped (Engine.Parse.parse builder cx strict stamp cs goal args)
  | none => .stop (.check "an input that is not code points")

/-- The grammar context of a parse context: the |Module| goal (B.1.1) and Annex B. -/
def grammarCx (cx : ParseCx) : Ctx := ⟨cx.module, cx.annexB⟩

/-- `n` with every node's stamp `k`, without parent indexes. -/
def restamp (k : Nat) : Node → Node
  | .mk _ lo hi p nt ps kids t => .mk k lo hi p nt ps (kids.attach.map fun ⟨c, h⟩ => (c.1, c.2.attach.map fun ⟨x, hx⟩ =>
      have : sizeOf x < sizeOf c := by
        rcases c with ⟨a, _ | y⟩ <;> simp at hx; subst hx; simp; omega
      have := Array.sizeOf_lt_of_mem h
      restamp k x)) t

/-- `Model.parse` at Impl, in context `cx`: `some (some n)` the Parse Node, `some none` no parse, `none`
undecided. -/
def parse (cx : ParseCx) (stamp : Nat) (src : Array MathVal) (goal : NtId)
    (args : List (ParamId × Bool)) : Option (Option Node) :=
  if !Engine.Parse.parseTablesOkThunk.get then none
  else if goal == NT.StringNumericLiteral.ctorIdx || goal == NT.StringIntegerLiteral.ctorIdx then
    match codePointsOf src, parseNumeric stamp src goal args with
    | some cs, some (some n) =>
      if shaped n && (builder.nt n == goal && builder.args n == Engine.Parse.paramsOfArgs args &&
          builder.span n == (0, cs.size) &&
          (verifyCodeNode cs (grammarCx cx) .numericString stamp (n.height + 1) n).isSome) then
        some (some n)
      else none
    | _, _ => match outcome 0 src goal args (grammarCx cx) cx.strict with
      | .ok n => some (some (restamp stamp n))
      | .noParse => some none
      | .stop _ => none
  else match outcome 0 src goal args (grammarCx cx) cx.strict with
    | .ok n => some (some (restamp stamp n))
    | .noParse => some none
    | .stop _ => none

/-- Whether `outcome` on `(src, goal, args)` stops at the parser's fuel or depth ceiling. -/
def isParseExhausted (cx : ParseCx) (src : Array MathVal) (goal : NtId)
    (args : List (ParamId × Bool)) : Bool :=
  if goal == NT.StringNumericLiteral.ctorIdx || goal == NT.StringIntegerLiteral.ctorIdx then false
  else match outcome 0 src goal args (grammarCx cx) cx.strict with
    | .stop .fuel | .stop .depth => true
    | _ => false

end Engine
