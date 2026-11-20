module

public import Engine.Parse.Core
public import Ecma.Grammar.StrictCode

@[expose] public section

/-!
# Strict mode code (§11.2.2) over a built tree

`view B d`: the builder's nodes as `Ecma.Grammar.strictCode` reads them, the walks to the depth bound `d`
(at least the tree's). A node of a nonterminal no syntactic rule defines is a token's lexical leaf: its own
nodes are not the tree's. `sloppyOk` is `NonStrictOk`: no node of an overlay production for non-strict
code (B.3.3, B.3.5) lies in strict mode code, from outside (`strict`) or by the tree.
-/

namespace Engine.Parse.Strict

open Ecma.Grammar

variable {N : Type} (B : Builder N)

/-- A node of the syntactic grammar (not a token's lexical leaf). -/
def syn (n : N) : Bool := (ruleIn .syntactic (B.nt n)).isSome

/-- The builder's nodes as §11.2.2 reads them, within depth `d`: a lexical leaf has no children. -/
def view (d : Nat) : NodeView N where
  isA n k := B.nt n == k.ctorIdx
  kids n := if syn B n then (B.kids n).toList.filterMap (·.2) else []
  span := B.span
  textIs n cs := (B.text n).toList == cs
  height _ := d

/-- Production `p` is an overlay's that applies only to non-strict code (`GL.sloppyIds`). -/
def sloppy (p : Nat) : Bool :=
  match prodOf [] p with
  | some P => P.grammar == .annexB && Gen.blocks.any fun b => b.kind matches .overlay _ _ .nonStrict && b.rules.contains P.rule
  | none => false

/-- No node of a non-strict overlay production lies in strict mode code, from outside (`strict`) or
by the tree (walked to depth `d`), `up` the node's ancestors, within depth `f`; none past it. -/
def sloppyOk (d : Nat) (strict : Bool) : Nat → List N → N → Option Bool
  | 0, _, _ => none
  | f + 1, up, t =>
    if !syn B t then some true
    else if sloppy (B.prod t) && (strict || strictCode (view B d) up t) then some false
    else ((view B d).kids t).foldlM (init := true) fun ok k => if ok then sloppyOk d strict f (t :: up) k else some false

end Engine.Parse.Strict
