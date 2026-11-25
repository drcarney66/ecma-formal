module

public import Engine.Parse.Core
public import Ecma.Model.NodeRel

@[expose] public section

/-!
# The occurrences of a production, tabulated

`occsBy p` is `Grammar.occsAt` of GL at production `p` (the nonterminal occurrences of its right-hand side
with their presences), from a table of GL's productions made once: what a Parse Node's children are
checked against (`Engine.shapeOk`).
-/

namespace Engine.Parse

open Ecma.Grammar

/-- The nonterminal occurrences of a production's right-hand side, with their presences (`Grammar.occsAt`'s). -/
def occsOfProd (p : Prod) : List (NT × Bool) := (p.altOf.map fun a => occsOf a.rhs p.mask).getD []

/-- The occurrences of GL's productions, by production id (none at a retired number). -/
def glOccs : Thunk (Array (List (NT × Bool))) := Thunk.mk fun _ => prods.map fun o => (o.map occsOfProd).getD []

/-- The occurrences of production `p`: GL's; none where there is no such production. -/
def occsBy (p : Nat) : List (NT × Bool) :=
  glOccs.get[p]?.getD []

end Engine.Parse
