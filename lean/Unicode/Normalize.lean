module

public import Unicode.Gen.NormalizationData
public import Unicode.Search

@[expose] public section

/-!
# Unicode normalization

The normalization forms of UAX #15 (Unicode §3.11), which
String.prototype.normalize (§22.1.3.15) performs (`Engine.normalizePoints`). They depend only
on the Unicode data.
-/

namespace Unicode

/-! ### The tables as Arrays (lever 3: bisection, `Unicode/Search.lean`) -/

/-- The decompositions, the combining classes' runs and the primary composites
of `Unicode/Gen/NormalizationData.lean` as Arrays. -/
def canonicalDecompositionsA : Array (Nat × List Nat) := ⟨canonicalDecompositions⟩
def compatibilityDecompositionsA : Array (Nat × List Nat) := ⟨compatibilityDecompositions⟩
def combiningClassRunsA : Array (Nat × Nat × Nat) := ⟨combiningClassRuns⟩
def primaryCompositesA : Array (Nat × Nat × Nat) := ⟨primaryComposites⟩

/-- The primary composites' key: the pair (first, second) as one number (each code
point is below 2^21). -/
@[macro_inline] def compositeKey (r : Nat × Nat × Nat) : Nat := r.1 * 0x200000 + r.2.1

/-- The mapping of _c_ in a decomposition table, by bisection (`lookupMappingA_eq`). -/
@[macro_inline] def lookupMappingA (table : Array (Nat × List Nat)) (c : Nat) : Option (List Nat) :=
  lookupSortedA table c

/-- The class of _c_ in the runs _runs_ (an Array in code point order, the runs
disjoint): the last run that starts at or before _c_, by bisection
(`classOf_eq`: the walk of the runs). -/
@[macro_inline] def classOf (runs : Array (Nat × Nat × Nat)) (c : Nat) : Nat :=
  match lastLE Prod.fst runs c with
  | some (_, last, k) => if c ≤ last then k else 0
  | none => 0

/-- The Canonical_Combining_Class of _c_ (`combiningClassRuns`; 0 when it is
in no run), by bisection of the runs (`combiningClass_eq`: their walk). -/
def combiningClass (c : Nat) : Nat := classOf combiningClassRunsA c

/-! ### Hangul syllables (Unicode §3.12) -/

/-- SBase, LBase, VBase, TBase, and LCount, VCount, TCount, NCount = VCount ×
TCount, SCount = LCount × NCount (the products evaluated: data constants). -/
def SBase : Nat := 0xAC00
def LBase : Nat := 0x1100
def VBase : Nat := 0x1161
def TBase : Nat := 0x11A7
def LCount : Nat := 19
def VCount : Nat := 21
def TCount : Nat := 28
def NCount : Nat := 588
def SCount : Nat := 11172

/-- Hangul Syllable Decomposition: the L, V and (when TIndex ≠ 0) T jamo of
the syllable _s_. -/
def decomposeHangul (s : Nat) : List Nat :=
  let SIndex := s - SBase
  let L := LBase + SIndex / NCount
  let V := VBase + (SIndex % NCount) / TCount
  let T := TBase + SIndex % TCount
  if T = TBase then [L, V] else [L, V, T]

/-- Hangul Syllable Composition of an L jamo and a V jamo, or of an LV
syllable and a T jamo. -/
def composeHangul (first second : Nat) : Option Nat :=
  if LBase ≤ first ∧ first < LBase + LCount ∧ VBase ≤ second ∧ second < VBase + VCount then
    some (SBase + ((first - LBase) * VCount + (second - VBase)) * TCount)
  else if SBase ≤ first ∧ first < SBase + SCount ∧ (first - SBase) % TCount = 0 ∧
      TBase < second ∧ second < TBase + TCount then
    some (first + (second - TBase))
  else none

/-! ### Decomposition, canonical ordering and composition -/

/-- The full canonical decomposition of _c_, or its full compatibility
decomposition when _compatibility_ is true. -/
def decompose (compatibility : Bool) (c : Nat) : List Nat :=
  if SBase ≤ c ∧ c < SBase + SCount then decomposeHangul c
  else match (if compatibility then lookupMappingA compatibilityDecompositionsA c else none) with
    | some m => m
    | none => (lookupMappingA canonicalDecompositionsA c).ucdOrSelf [c]

/-- Put the non-starter _c_ of class _k_ into _before_ (the characters before
it with their classes, nearest first): after every character before it whose
class is at most _k_, and before those of greater class (D108, D109). -/
def insertByClass (c k : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(c, k)]
  | (d, kd) :: before => if k < kd then (d, kd) :: insertByClass c k before else (c, k) :: (d, kd) :: before

/-- The Canonical Ordering Algorithm (D109): the stable sort of each run of
non-starters by Canonical_Combining_Class. -/
def canonicalOrder (text : List Nat) : List Nat :=
  (text.foldl (fun before c =>
      let k := combiningClass c
      if k = 0 then (c, 0) :: before else insertByClass c k before) []).reverse.map (·.1)

/-- The entry of the pair (_first_, _second_) in the table _table_ (in the order of
`compositeKey`), by bisection on the pair's key (`compositeOf_eq`: the walk of the
table). -/
@[macro_inline] def compositeOf (table : Array (Nat × Nat × Nat)) (first second : Nat) : Option Nat :=
  match lastLE compositeKey table (first * 0x200000 + second) with
  | some (a, b, s) => if first = a ∧ second = b then some s else none
  | none => none

/-- The primary composite of _first_ and _second_, if any: the table's entry of
the pair, found by bisection (`primaryComposite_eq`: the walk of the table). -/
def primaryComposite (first second : Nat) : Option Nat :=
  match composeHangul first second with
  | some s => some s
  | none => compositeOf primaryCompositesA first second

/-- The state of the Canonical Composition Algorithm: the characters before
the last starter (nearest first), the last starter (`none` before the first
one), the characters after it (nearest first), and the class of the last of
them (the starter's class 0 when there is none). -/
structure CompositionState where
  done : List Nat := []
  starter : Option Nat := none
  after : List Nat := []
  lastClass : Nat := 0

/-- The Canonical Composition Algorithm (D117) for the next character _c_ of
the canonically ordered text: if there is a last starter _L_, _c_ is not
blocked from it (no character between them has class 0 or a class not less
than _c_'s), and _L_ and _c_ have a primary composite, replace _L_ with the
composite; otherwise append _c_ (a new starter when its class is 0). -/
def CompositionState.push (state : CompositionState) (c : Nat) : CompositionState :=
  let k := combiningClass c
  let composite := match state.starter with
    | some L => if state.after.isEmpty ∨ state.lastClass < k then primaryComposite L c else none
    | none => none
  match composite with
  | some composite => { state with starter := some composite }
  | none =>
    if k = 0 then
      { done := state.after ++ state.starter.toList ++ state.done, starter := some c,
        after := [], lastClass := 0 }
    else { state with after := c :: state.after, lastClass := k }

/-- The Canonical Composition Algorithm of a canonically ordered text. -/
def canonicalComposition (text : List Nat) : List Nat :=
  let state := text.foldl CompositionState.push {}
  (state.after ++ state.starter.toList ++ state.done).reverse

/-- The normalization forms of UAX #15. -/
inductive NormalizationForm where
  | NFC | NFD | NFKC | NFKD
  deriving DecidableEq, Repr

/-- The text normalized into the normalization form _form_. -/
def normalize (form : NormalizationForm) (text : List Nat) : List Nat :=
  let compatibility := form = .NFKC ∨ form = .NFKD
  let decomposed := canonicalOrder (text.flatMap (decompose compatibility))
  if form = .NFC ∨ form = .NFKC then canonicalComposition decomposed else decomposed

end Unicode

