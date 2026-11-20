module

public import Ecma.Grammar.Print
public import Ecma.Grammar.Gen.Index

@[expose] public section

/-!
# GL's right-hand sides by production id

`prods` is the pinned grammars' right-hand sides by production id, the
numbering spec/formal/prod-ids.txt gives (`prodsById`).
-/

namespace Engine.Parse

open Ecma.Grammar

/-- GL's right-hand sides by production id (`GL.byId` of the specification's GL): a `ProdId` is an
index, none at a retired number. -/
def prods : Array (Option Prod) := prodsById Gen.grammars Gen.prodIds Gen.prodNext

end Engine.Parse
