module

public import Unicode.Gen.CaseData
public import Unicode.Search
public import Unicode.Gen.BinaryProperties1
public import Unicode.Gen.BinaryProperties2
public import Unicode.Gen.BinaryProperties3

@[expose] public section

/-!
# Unicode Default Case Conversion

toLowercase and toUppercase (Unicode §3.13) with the locale-insensitive full
case mappings and the context Final_Sigma, which String.prototype.toLowerCase
and toUpperCase perform and which are the default host's locale case mapping
(`Host.localeCaseMapping`). They depend only on the Unicode data.
-/

namespace Unicode

/-! ### The tables as Arrays (lever 3: bisection, `Unicode/Search.lean`) -/

/-- The case runs of `Unicode/Gen/CaseData.lean` as Arrays. -/
def lowercaseRunsA : Array CaseRun := ⟨lowercaseRuns⟩
def uppercaseRunsA : Array CaseRun := ⟨uppercaseRuns⟩
def simpleCaseFoldingRunsA : Array CaseRun := ⟨simpleCaseFoldingRuns⟩

/-- The multi-code-point mappings and the case folding preimages as Arrays. -/
def lowercaseSpecialA : Array (Nat × List Nat) := ⟨lowercaseSpecial⟩
def uppercaseSpecialA : Array (Nat × List Nat) := ⟨uppercaseSpecial⟩

/-- The ranges of Cased and Case_Ignorable as Arrays. -/
def casedA : Array (Nat × Nat) := ⟨Binary.«Cased»⟩
def caseIgnorableA : Array (Nat × Nat) := ⟨Binary.«Case_Ignorable»⟩

/-- The mapping of _c_ by the runs _runs_ (an Array in code point order, the
runs disjoint): the last run that starts at or before _c_, by bisection. -/
@[macro_inline] def lookupRunsA (runs : Array CaseRun) (c : Nat) : Option Nat :=
  match lastLE CaseRun.first runs c with
  | some r => if c ≤ r.last ∧ (c - r.first) % r.stride = 0 then some (c + r.delta).toNat else none
  | none => none

/-- Whether _c_ is in one of the ranges (an Array in code point order, the
ranges disjoint): the last range that starts at or before _c_, by bisection
(`inRangesA_eq`: `inRanges`' walk). -/
@[macro_inline] def inRangesA (ranges : Array (Nat × Nat)) (c : Nat) : Bool :=
  match lastLE Prod.fst ranges c with
  | some (_, last) => decide (c ≤ last)
  | none => false

/-- The property Cased (DerivedCoreProperties.txt): the binary property table
of `\p{Cased}`, from the same Unicode release as every other table, by
bisection (`isCased_eq`). -/
def isCased (c : Nat) : Bool := inRangesA casedA c

/-- The property Case_Ignorable (DerivedCoreProperties.txt): the binary
property table of `\p{Case_Ignorable}`, by bisection (`isCaseIgnorable_eq`). -/
def isCaseIgnorable (c : Nat) : Bool := inRangesA caseIgnorableA c

/-- The full case mapping of _c_ by the runs and the multi-code-point mappings
(Arrays in code point order, searched by bisection: `fullMapping_eq`). -/
def fullMapping (runs : Array CaseRun) (special : Array (Nat × List Nat)) (c : Nat) : List Nat :=
  match lookupSortedA special c with
  | some m => m
  | none => [(lookupRunsA runs c).ucdOrSelf c]

/-- Whether a sequence of zero or more Case_Ignorable code points and then a
Cased one starts _cs_: `(\p{Case_Ignorable})* \p{cased}` of Table 3-17 with
its `*` possessive, as Unicode 17.0.0 §3.13.1 fixes it: "The
regular-expression operator * in Table 3-17 is “possessive,” consuming as many
characters as possible, with no backup. This is significant in the case of
Final_Sigma, because the sets of case-ignorable and cased characters are not
disjoint: for example, they both contain U+0345 COMBINING GREEK YPOGEGRAMMENI.
Thus, the Before condition is not satisfied if C is preceded by only U+0345,
but would be satisfied by the sequence <capital-alpha, ypogegrammeni>.
Similarly, the After condition is satisfied if C is only followed by
ypogegrammeni, but would not satisfied by the sequence <ypogegrammeni,
capital-alpha>." So `*` takes every Case_Ignorable code point, and the one
after them must be Cased. The Before context `\p{cased} (\p{Case_Ignorable})*`
read from C backwards (_before_ is nearest first) is the same test. -/
def casedAfterIgnorable : List Nat → Bool
  | [] => false
  | c :: cs => if isCaseIgnorable c then casedAfterIgnorable cs else isCased c

/-- The context Final_Sigma (Unicode §3.13.1, Table 3-17) of a code point with
the code points _before_ it (nearest first) and _after_ it: "C is preceded by
a sequence consisting of a cased letter and then zero or more case-ignorable
characters, and C is not followed by a sequence consisting of zero or more
case-ignorable characters and then a cased letter", with Before C
`\p{cased} (\p{Case_Ignorable})*` and After C
`! ( (\p{Case_Ignorable})* \p{cased} )`, `*` possessive
(`casedAfterIgnorable`). -/
def finalSigma (before after : List Nat) : Bool :=
  casedAfterIgnorable before && !casedAfterIgnorable after

/-- toLowercase ( _X_ ) (Unicode §3.13, D139, R2): each code point is mapped to
its full lowercase mapping; U+03A3 GREEK CAPITAL LETTER SIGMA in the context
Final_Sigma maps to U+03C2 GREEK SMALL LETTER FINAL SIGMA (SpecialCasing.txt).
_before_ holds the code points already mapped, nearest first. -/
def toLowercase (before : List Nat) : List Nat → List Nat
  | [] => []
  | c :: after =>
    (if c = 0x3A3 ∧ finalSigma before after then [0x3C2]
     else fullMapping lowercaseRunsA lowercaseSpecialA c) ++ toLowercase (c :: before) after

/-- toUppercase ( _X_ ) (Unicode §3.13, D139, R1): each code point is mapped to
its full uppercase mapping (SpecialCasing.txt has no language-insensitive
conditional uppercase mapping). -/
def toUppercase (text : List Nat) : List Nat :=
  text.flatMap (fullMapping uppercaseRunsA uppercaseSpecialA)

end Unicode

