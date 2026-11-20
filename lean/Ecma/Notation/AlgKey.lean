module

public import Ecma.Notation.Syntax

@[expose] public section

/-!
# An algorithm id's key

`Src.algKey`: the key a program's indexes find an algorithm by; `Src.keyId`, the id of index
below 4096 with that key.
-/

namespace Ecma

/-- A key for an `AlgId`. -/
def Src.algKey (a : AlgId) : Nat := a.clause * 4096 + a.idx

/-- The id of index below 4096 with `a`'s key. -/
def Src.keyId (a : AlgId) : AlgId := ⟨Src.algKey a / 4096, Src.algKey a % 4096⟩

end Ecma
