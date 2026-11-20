module

public import Engine.Parse.Core
public import Ecma.Model.NodeRel

@[expose] public section

/-!
# The occurrences of a production, tabulated

`occsBy (readingOccs rd) p` is `Grammar.occsAt` of GL and the readings `rd` at production `p` (the nonterminal
occurrences of its right-hand side with their presences), from a table of GL's productions made once and one of
the readings' made per parse: what a Parse Node's children are checked against (`Engine.shapeOk`).
-/

namespace Engine.Parse

open Ecma.Grammar

/-- The nonterminal occurrences of a production's right-hand side, with their presences (`Grammar.occsAt`'s). -/
def occsOfProd (p : Prod) : List (NT × Bool) := (p.altOf.map fun a => occsOf a.rhs p.mask).getD []

/-- The occurrences of GL's productions, by production id (none at a retired number). -/
def glOccs : Thunk (Array (List (NT × Bool))) := Thunk.mk fun _ => prods.map fun o => (o.map occsOfProd).getD []

/-- The occurrences of the readings' productions, numbered past GL's numbers. -/
def readingOccs (rd : List RuleReading) : Array (List (NT × Bool)) := (readingProds rd).map occsOfProd

/-- The occurrences of production `p`: GL's, or past GL's numbers a reading's (`rs`); none where there is no
such production. -/
def occsBy (rs : Array (List (NT × Bool))) (p : Nat) : List (NT × Bool) :=
  let t := glOccs.get
  if p < t.size then t[p]?.getD [] else rs[p - t.size]?.getD []

end Engine.Parse
