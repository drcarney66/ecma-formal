module

public import Engine.Parse.Kernel

@[expose] public section

/-!
# The tripwire: what a Parse Node shows, checked against GL

`check` reads a finished tree through the builder's views and lists each node whose production,
nonterminal, parameters, children, span, stamp or text disagrees with GL: the production's
left-hand side is the node's nonterminal, an Annex B production is an alternative in effect in the
parse context, its guard holds, one child entry per written
nonterminal item with the presence mask, each child's parameters `applyArgs` of the node's, the
children's spans in order inside the node's, the invocation's stamp, and the text the span's
code points. Code point grammars only: spans are code point offsets.
-/

namespace Engine.Parse

open Ecma.Grammar

variable {N : Type}

/-- The child entries a right-hand side has: each written nonterminal item, with whether it is
present under `mask`, and its arguments. -/
def expectedKids : List Item → List Bool → List (Nat × Bool × List Arg)
  | [], _ => []
  | .sym (.nt n args) true :: is, b :: ms => (n.ctorIdx, b, args) :: expectedKids is ms
  | .sym (.t _) true :: is, _ :: ms => expectedKids is ms
  | .sym (.nt n args) false :: is, ms => (n.ctorIdx, true, args) :: expectedKids is ms
  | .butNot (.nt n args) _ :: is, ms => (n.ctorIdx, true, args) :: expectedKids is ms
  | _ :: is, ms => expectedKids is ms

/-- The code point and syntactic grammars. -/
def grammarIds : List GrammarId := [.numericString, .lexical, .syntactic, .regExp, .json]

/-- Production's right-hand side `P` is an alternative in effect in some grammar in context `cx`. -/
def inEffect (cx : Ctx) (P : Prod) : Bool :=
  grammarIds.any fun g => ((effAlts g cx P.rule.lhs.ctorIdx).getD []).any fun e =>
    e.wg == P.grammar && e.idx == P.alt && e.rule == P.rule

/-- The failures of one node, without its descendants. -/
def checkNode (B : Builder N) (cx : Ctx) (cs : Array Nat) (stamp : Nat) (n : N) :
    List String := Id.run do
  let (lo, hi) := B.span n
  let pre := s!"node {B.prod n} [{lo},{hi}): "
  let mut errs : List String := []
  if B.stamp n != stamp then errs := errs ++ [pre ++ "stamp"]
  if !(lo ≤ hi && hi ≤ cs.size) then errs := errs ++ [pre ++ "span"]
  else if B.text n != points cs lo hi then errs := errs ++ [pre ++ "text"]
  let some P := prodOf (B.prod n) | return errs ++ [pre ++ "no such production"]
  if P.rule.lhs.ctorIdx != B.nt n then errs := errs ++ [pre ++ "nonterminal"]
  if P.grammar == .annexB && !inEffect cx P then errs := errs ++ [pre ++ "an Annex B production not in effect"]
  let some a := (writtenAlts P.rule)[P.alt]? | return errs ++ [pre ++ "no such alternative"]
  if !a.guard.all (Guard.holds (B.args n)) then errs := errs ++ [pre ++ "guard"]
  let want := expectedKids a.rhs P.mask
  let kids := (B.kids n).toList
  if want.length != kids.length then return errs ++ [pre ++ "child count"]
  let mut pos := lo
  for ((wn, wp, wargs), (kn, kc)) in want.zip kids do
    if wn != kn then errs := errs ++ [pre ++ "child nonterminal"]
    match kc, wp with
    | none, false => pure ()
    | some c, true =>
      if B.nt c != wn then errs := errs ++ [pre ++ "child's own nonterminal"]
      if B.args c != applyArgs (B.args n) wargs then errs := errs ++ [pre ++ "child parameters"]
      let (a, b) := B.span c
      if !(pos ≤ a && a ≤ b && b ≤ hi) then errs := errs ++ [pre ++ "child span"]
      pos := b
    | _, _ => errs := errs ++ [pre ++ "child presence"]
  return errs

end Engine.Parse
