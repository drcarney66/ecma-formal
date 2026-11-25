module

public import Ecma.Grammar.Print
public import Ecma.Grammar.Gen.Index

@[expose] public section

/-!
# GL's right-hand sides by production id

`prods` is the pinned grammars' right-hand sides by production id (`prodsById`).
-/

namespace Engine.Parse

open Ecma.Grammar

/-- GL's right-hand sides by production id (`GL.byId` of the specification's GL). -/
def prods : Array (Option Prod) := prodsById Gen.grammars Gen.prodIds Gen.prodNext

end Engine.Parse
