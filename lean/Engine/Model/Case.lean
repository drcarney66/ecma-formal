module

public import Unicode.Case

@[expose] public section

/-!
# Unicode case operations on code points

The Model's case operations over natural numbers, from the generated UCD tables
(`Unicode.CaseData`): Ref and Bare convert their mathematical values to
these. A result above 0x10FFFF is dropped; the tables have none.
-/

namespace Engine

/-- The largest code point. -/
abbrev maxPoint : Nat := 0x10FFFF

/-- The simple case folding of `c` (CaseFolding.txt, status C or S). -/
def scfPoint? (c : Nat) : Option Nat :=
  if c ≤ maxPoint then (Unicode.lookupRunsA Unicode.simpleCaseFoldingRunsA c).filter (· ≤ maxPoint)
  else none

/-- toLowercase of a sequence of code points (Unicode §3.13, Final_Sigma in context). -/
def lowerPoints (cs : List Nat) : List Nat :=
  (Unicode.toLowercase [] cs).filter (· ≤ maxPoint)

/-- toUppercase of a sequence of code points (Unicode §3.13). -/
def upperPoints (cs : List Nat) : List Nat :=
  (Unicode.toUppercase cs).filter (· ≤ maxPoint)

end Engine
