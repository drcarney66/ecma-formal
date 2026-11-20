module

public import Ecma.Model
public import Unicode.Normalize

@[expose] public section

namespace Engine

/-- The instance's normalization form for `Ecma.NormForm`. -/
def normForm : Ecma.NormForm → Unicode.NormalizationForm
  | .NFC => .NFC
  | .NFD => .NFD
  | .NFKC => .NFKC
  | .NFKD => .NFKD

/-- The code points normalized into the form by the UCD tables; results above 0x10FFFF dropped. -/
def normalizePoints (f : Ecma.NormForm) (cs : List Nat) : List Nat :=
  (Unicode.normalize (normForm f) cs).filter (· ≤ 0x10FFFF)

end Engine
