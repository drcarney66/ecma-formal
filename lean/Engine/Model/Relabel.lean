module

public import Engine.Model.Parse

@[expose] public section

/-!
# A cover's covered node at Impl

`relabel` is `Model.cover` at Impl (§5.1.5's reparse, `Ecma.reparse`), answering where the covered production has
the cover's own right-hand side: CoverParenthesizedExpressionAndArrowParameterList : `( Expression )` as
ParenthesizedExpression, and CoverCallExpressionAndAsyncArrowHead : MemberExpression Arguments as
CallMemberExpression. The covered node is the cover's subtree relabelled, as `parse` builds it: the children
copied with spans from the cover's start, the new invocation's stamp and text views over the cover's code
points; the root the goal's production with the cover's parameters (`Ecma.coverArgs`). The root is checked
against GL (`Parse.checkNode`) and, under Annex B, the tree's NonStrictOk (`Parse.Strict.sloppyOk`); every
node's children are checked to be its production's occurrences (`shaped`).
-/

namespace Engine.Model.Relabel

open Engine.Model Ecma.Grammar
open Ecma (NtId ParamId ParseCx)

/-- The covers relabelled, each with the goal whose production has the cover's right-hand side. -/
def pairs : List (NtId × NtId) :=
  [(NT.CoverParenthesizedExpressionAndArrowParameterList.ctorIdx, NT.ParenthesizedExpression.ctorIdx),
   (NT.CoverCallExpressionAndAsyncArrowHead.ctorIdx, NT.CallMemberExpression.ctorIdx)]

/-- `n`'s tree with every node's stamp `k`, its spans from `lo`, its text views over `cs`, without parent
indexes. -/
def shift (k lo : Nat) (cs : Array Nat) : Node → Node
  | .mk _ i j p nt ps kids _ => .mk k (i - lo) (j - lo) p nt ps (kids.attach.map fun ⟨c, h⟩ =>
      (c.1, c.2.attach.map fun ⟨x, hx⟩ =>
        have : sizeOf x < sizeOf c := by
          rcases c with ⟨a, _ | y⟩ <;> simp at hx; subst hx; simp; omega
        have := Array.sizeOf_lt_of_mem h
        shift k lo cs x)) (Engine.Parse.view cs (i - lo) (j - lo))

/-- A right-hand side's items under the presence mask: the absent optional symbols dropped, the present ones
not optional. -/
def present : List Item → List Bool → List Item
  | .sym x true :: is, b :: ms => if b then .sym x false :: present is ms else present is ms
  | i :: is, ms => i :: present is ms
  | [], _ => []

/-- The production of goal `k` with the right-hand side of production `p`, in context `gx`: `k`'s only
alternative in effect, unguarded and without optional symbols, when its right-hand side is `p`'s under
`p`'s mask. -/
def target (gx : Ctx) (p k : Nat) : Option Nat := do
  let P ← Engine.Parse.prodOf p
  let a ← P.altOf
  let goalNt ← Engine.Parse.ruleNt .syntactic k
  let es := Engine.Parse.altsOf gx .syntactic goalNt
  let [e] := es | none
  guard (e.alt.guard.isEmpty && e.alt.opts == 0 && e.alt.rhs == present a.rhs P.mask)
  Engine.Parse.prodIdOf e []

/-- The covered node of cover `n` at goal `k`, invocation `st`, with the parameters `args`, in context `cx`:
`n`'s subtree relabelled, its root checked; none to decline. -/
def relabel (cx : ParseCx) (st : Nat) (n : Node) (k : NtId) (args : List (ParamId × Bool)) : Option Node :=
  if !Engine.Parse.parseTablesOkThunk.get then none else
  match n with
  | .mk _ lo hi p nt _ kids t => do
    guard (pairs.contains (nt, k))
    let gx := grammarCx cx
    let p' ← target gx p k
    let cs := t.toArray
    let r := Node.mk st 0 (hi - lo) p' k (Engine.Parse.paramsOfArgs args)
      (kids.map fun (m, c) => (m, c.map (shift st lo cs))) (Engine.Parse.view cs 0 cs.size)
    guard (Engine.Parse.checkNode builder gx cs st r).isEmpty
    let d := Engine.Parse.Syntax.depth cs.size + 1
    guard (!gx.annexB.any || Engine.Parse.Strict.sloppyOk builder d cx.strict d [] r == some true)
    guard (shaped r)
    return r

end Engine.Model.Relabel
