module

public import Engine.Proofs.Pins.Gen.Eq

@[expose] public section

/-!
# The equality test of code

`Code.optEqB`, an optional unit's code tested instruction by instruction (`Engine.Proofs.Pins.Gen.Eq`: generated,
with `Ins.eqB`, `Op.eqB`, `Stmt.eqB`, …), with its soundness: the test holds of equal values only (`Engine.Pins.pin`
turns an evaluated equality test into an equation).
-/

open Engine.Pins

namespace Ecma.Machine

def Code.optEqB (a b : Option Code) : Bool := EqB.eqB a b

theorem Code.optEqB_sound (a b : Option Code) (h : Code.optEqB a b = true) : a = b := EqB.sound a b h

end Ecma.Machine
