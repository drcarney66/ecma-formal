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

`parse` is `Model.parse` at Impl. StringNumericLiteral and StringIntegerLiteral go to the numeric
string accelerator, every other goal to `Parse` with Bare's Parse Nodes as its nodes: a Parse
Node, "no parse" (after a complete decision of the grammar), or undecided for a stop. At |JSONText|,
an input ECMA-404's recognizer (`Engine.JsonText.text`) rejects is "no parse" without Parse; so is an
input whose first code point no derivation of a lexical goal starts with (`firstSet`).

The code point classes (<USP>, ID_Start, ID_Continue) are the instance's (`Engine.Model.codePrims`).
The grammar is the parse context's (Annex B's overlays in effect, the |Module| goal); under Annex B a
RegExp goal is Parse's committed parse with B.1.2's group-number condition (`Parse.Code.run`), and,
outside a Module, B.1.1's HTML-like comments are in the lexer's trivia (`Parse.Lex.htmlAt`).

Accelerator debt: soundness and completeness against `Ecma.Model.ParseLaws`, owed (over Parse's builder, and
for this instance); soundness at the code point goals and JSONText's "no parse" are proved outside
this repository.
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
  idStart := some idStart
  idContinue := some idContinue

/-- The code points of a parse's input; none if one is not a code point. -/
def codePointsOf (src : Array MathVal) : Option (Array Nat) :=
  src.mapM fun | .int i => if 0 ≤ i ∧ i ≤ 0x10FFFF then some i.toNat else none | _ => none

/-- The goal is |JSONText| and `cs` is not a JSON text: no derivation. -/
def noJSON (goal : NtId) (cs : Array Nat) : Bool :=
  goal == NT.JSONText.ctorIdx && !Engine.JsonText.text ⟨(· == ·), (· < ·)⟩ cs.toList

/-- The code points a lexical goal's derivations start with, where checked: |StringLiteral|'s `"` and `'`. -/
def firstSet (goal : NtId) : Option (List Int) :=
  if goal == NT.StringLiteral.ctorIdx then some [34, 39] else none

/-- `src` starts with a code point outside the goal's `firstSet`: no derivation. -/
def noFirst (goal : NtId) (src : Array MathVal) : Bool :=
  match firstSet goal, src[0]? with
  | some fs, some (MathVal.int c) => !fs.contains c
  | _, _ => false

/-- The children `i` on of `kids` are the occurrences `os`, in order: a present occurrence's slot and its child
have its nonterminal, an absent one's slot has its nonterminal and no child, and there are no more of either. -/
def slotsOk (kids : Array (NtId × Option Node)) : List (NT × Bool) → Nat → Bool
  | [], i => i == kids.size
  | (n, b) :: os, i => match kids[i]? with
    | some (t, some (.mk _ _ _ _ m _ _ _)) => b && t == n.ctorIdx && m == n.ctorIdx && slotsOk kids os (i + 1)
    | some (t, none) => !b && t == n.ctorIdx && slotsOk kids os (i + 1)
    | none => false

/-- At every node of the tree `n`, the children are the occurrences of the node's production (`occs`, by
production id) with their presences (`slotsOk`): what `Model.NodeLaws.child_parse` says of a parse. One pass,
no text compared. -/
def shapeOk (occs : Nat → List (NT × Bool)) : Node → Bool
  | .mk _ _ _ p _ _ kids _ => slotsOk kids (occs p) 0 && kids.attach.all fun ⟨c, h⟩ => c.2.attach.all fun ⟨x, hx⟩ =>
      have : sizeOf x < sizeOf c := by
        rcases c with ⟨a, _ | y⟩ <;> simp at hx; subst hx; simp; omega
      have := Array.sizeOf_lt_of_mem h
      shapeOk occs x

/-- The check of a parse: every node's children are its production's occurrences. -/
def shaped : Node → Bool := shapeOk Engine.Parse.occsBy

/-- An outcome whose Parse Node passes `ok`; a stop where it does not. -/
@[reducible] def checked (ok : Node → Bool) : Engine.Parse.Outcome Node → Engine.Parse.Outcome Node
  | .ok n => if ok n then .ok n else .stop (.check "a Parse Node whose children are not its production's")
  | o => o

/-- Parse's outcome for a goal at Bare, in context `cx`, `strict` its source text being strict mode
code from outside; "no parse" at a first code point outside the goal's `firstSet`, and at |JSONText|
on an input that is not a JSON text; a stop where a node's children are not its production's
occurrences (`shaped`). -/
def outcome (stamp : Nat) (src : Array MathVal) (goal : NtId) (args : List (ParamId × Bool))
    (cx : Ctx := ⟨false, {}⟩) (strict : Bool := false) :
    Engine.Parse.Outcome Node :=
  if noFirst goal src then .noParse else
  match codePointsOf src with
  | some cs => if noJSON goal cs then .noParse else
      checked shaped (Engine.Parse.parse builder cx strict stamp cs goal args)
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
undecided (where a node's children are not its production's occurrences: `shaped`, in `outcome` and here
for a numeric string's). Strictness from outside only bears on Annex B's productions, and json on no parse.
Parse runs as invocation 0, its tree restamped and its root indexed (`indexed`). -/
def parse (cx : ParseCx) (stamp : Nat) (src : Array MathVal) (goal : NtId)
    (args : List (ParamId × Bool)) : Option (Option Node) :=
  if goal == NT.StringNumericLiteral.ctorIdx || goal == NT.StringIntegerLiteral.ctorIdx then
    match parseNumeric stamp src goal args with
    | some (some n) => if shaped n then some (some n) else none
    | o => o
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
