module

public import Ecma.Notation.Early
public import Ecma.Notation.Tables
public import Ecma.Notation.Realm
public import Ecma.Lower.Src

@[expose] public section

/-!
# The program with implementation extras
-/

namespace Ecma

/-- The program of `s`, with the algorithms `extras` where `s` defines none. -/
def Src.expanded (s : Src) (extras : AlgId → Option Alg) : Prog :=
  let P := s.prog
  { P with alg := fun a => (P.alg a).or (extras a) }

end Ecma
