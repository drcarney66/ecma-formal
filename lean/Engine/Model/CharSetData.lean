module

public import Engine.Model.Bare
public import Engine.Model.OMapLaws
public import Engine.Model.PropSets
public import Engine.Model.Case

@[expose] public section

/-!
# Range and sparse case-folding operations for `Engine.Model.CharSet`
-/

namespace Engine.Model

/-- The largest Unicode code point. -/
def maxCodePoint : Nat := 0x10FFFF

/-- A mathematical value as a Unicode code point `0 .. 0x10FFFF`, if it is one. -/
@[inline] def point? : MathVal → Option Nat
  | .int i => if 0 ≤ i ∧ i ≤ maxCodePoint then some i.toNat else none
  | _ => none

/-- Canonical normalized interval list check: sorted, disjoint, non-adjacent, all `≤ 0x10FFFF`. -/
def rangeListOk (minLo : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (lo, hi) :: r => minLo ≤ lo && lo ≤ hi && hi ≤ maxCodePoint && rangeListOk (hi + 2) r

/-- Append interval `(lo, hi)` (with `lo ≥ last.1`) onto reversed accumulator, merging if contiguous/overlapping. -/
@[inline] def pushRange (acc : List (Nat × Nat)) (lo hi : Nat) : List (Nat × Nat) :=
  match acc with
  | (plo, phi) :: rest =>
    if lo ≤ phi + 1 then (plo, max phi hi) :: rest else (lo, hi) :: acc
  | [] => [(lo, hi)]

/-- Union of two normalized range lists. -/
def unionRangesLoop (acc : List (Nat × Nat)) : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], ys => (ys.foldl (fun a r => pushRange a r.1 r.2) acc).reverse
  | xs, [] => (xs.foldl (fun a r => pushRange a r.1 r.2) acc).reverse
  | (a1, b1) :: xs', (a2, b2) :: ys' =>
    if a1 ≤ a2 then unionRangesLoop (pushRange acc a1 b1) xs' ((a2, b2) :: ys')
    else unionRangesLoop (pushRange acc a2 b2) ((a1, b1) :: xs') ys'

def unionRanges (xs ys : Array (Nat × Nat)) : Array (Nat × Nat) :=
  (unionRangesLoop [] xs.toList ys.toList).toArray

/-- Complement of a normalized range list in `0 .. 0x10FFFF`. -/
def complRangesLoop (cur : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) → List (Nat × Nat)
  | [] => (if cur ≤ maxCodePoint then (cur, maxCodePoint) :: acc else acc).reverse
  | (lo, hi) :: r =>
    let acc' := if cur < lo then (cur, lo - 1) :: acc else acc
    complRangesLoop (hi + 1) acc' r

def complRanges (xs : Array (Nat × Nat)) : Array (Nat × Nat) :=
  (complRangesLoop 0 [] xs.toList).toArray

def diffRanges (xs ys : Array (Nat × Nat)) : Array (Nat × Nat) :=
  complRanges (unionRanges (complRanges xs) ys)

def interRanges (xs ys : Array (Nat × Nat)) : Array (Nat × Nat) :=
  complRanges (unionRanges (complRanges xs) (complRanges ys))

/-- Collapse sorted ascending `Nat`s (≤ 0x10FFFF) into normalized ranges. -/
def coalescePoints (ps : List Nat) : Array (Nat × Nat) :=
  (ps.foldl (fun acc c => pushRange acc c c) []).reverse.toArray

/-- Coalesce already strictly-increasing `PropSets` ranges (`b < c` may have `b + 1 = c`). -/
def coalesceRanges (rs : List (Nat × Nat)) : Array (Nat × Nat) :=
  (rs.foldl (fun acc r => pushRange acc r.1 r.2) []).reverse.toArray

def rangesCount (rs : Array (Nat × Nat)) : Nat :=
  rs.foldl (fun acc (lo, hi) => acc + (hi + 1 - lo)) 0

def rangesGet (rs : Array (Nat × Nat)) (idx : Nat) : Option Nat :=
  let rec go (i k : Nat) : Option Nat :=
    if h : i < rs.size then
      let (lo, hi) := rs[i]
      let len := hi + 1 - lo
      if k < len then some (lo + k) else go (i + 1) (k - len)
    else none
  go 0 idx

/-! ### Sparse case-folding tables from `Unicode.CaseData` -/

/-- Expand a single `CaseRun`'s domain code points `first, first + stride, … ≤ last` by structural fuel. -/
def runPointsFuel (fuel c last stride : Nat) (acc : List Nat) : List Nat :=
  match fuel with
  | 0 => acc.reverse
  | k + 1 =>
    if c ≤ last then runPointsFuel k (c + stride) last stride (c :: acc)
    else acc.reverse

/-- All `(c, scf c)` pairs where `c` is in `simpleCaseFoldingRuns` (`c` ascending). -/
def scfPairsList : List (Nat × Nat) :=
  _root_.Unicode.simpleCaseFoldingRuns.flatMap fun r =>
    let fuel := if 0 < r.stride ∧ r.first ≤ r.last then (r.last - r.first) / r.stride + 1 else 0
    (runPointsFuel fuel r.first r.last r.stride []).map fun c => (c, ((c : Int) + r.delta).toNat)

def scfPairs : Array (Nat × Nat) := scfPairsList.toArray
def scfDomainRanges : Array (Nat × Nat) := coalescePoints (scfPairsList.map Prod.fst)

/-- Non-Unicode `Canonicalize` pairs `(c, d)` with `d ≠ c`, `c` ascending. -/
def nonUCanonPairsList : List (Nat × Nat) :=
  let sp := _root_.Unicode.uppercaseSpecialA
  _root_.Unicode.uppercaseRuns.flatMap fun r =>
    let fuel := if 0 < r.stride ∧ r.first ≤ r.last then (r.last - r.first) / r.stride + 1 else 0
    (runPointsFuel fuel r.first r.last r.stride []).filterMap fun c =>
      match _root_.Unicode.lookupSortedA sp c with
      | some _ => none
      | none =>
        let d := ((c : Int) + r.delta).toNat
        if d ≤ 0xFFFF && !(128 ≤ c && d < 128) && d != c then some (c, d) else none

def nonUCanonPairs : Array (Nat × Nat) := nonUCanonPairsList.toArray
def nonUCanonDomainRanges : Array (Nat × Nat) := coalescePoints (nonUCanonPairsList.map Prod.fst)

/-- Merge two `(c, d)` lists sorted by `(d, c)` using structural fuel. -/
def mergePairsDCFuel : Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, xs, _ => xs
  | _, [], ys => ys
  | _, xs, [] => xs
  | k + 1, x :: xs', y :: ys' =>
    if x.2 < y.2 || (x.2 == y.2 && x.1 ≤ y.1) then x :: mergePairsDCFuel k xs' (y :: ys')
    else y :: mergePairsDCFuel k (x :: xs') ys'

def mergePairsListDC : List (List (Nat × Nat)) → List (List (Nat × Nat))
  | a :: b :: r => mergePairsDCFuel (a.length + b.length + 1) a b :: mergePairsListDC r
  | zs => zs

def sortPairsDCGo : Nat → List (List (Nat × Nat)) → List (Nat × Nat)
  | _, [] => []
  | _, [x] => x
  | 0, x :: _ => x
  | k + 1, zs => sortPairsDCGo k (mergePairsListDC zs)

def sortPairsDC (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  sortPairsDCGo xs.length (xs.map ([·]))

def groupPre (curD : Nat) (curCs : List Nat) (hasCur : Bool) (acc : List (Nat × Array Nat)) :
    List (Nat × Nat) → List (Nat × Array Nat)
  | [] => (if hasCur then (curD, curCs.reverse.toArray) :: acc else acc).reverse
  | (c, d) :: r =>
    if !hasCur then groupPre d [c] true acc r
    else if d == curD then
      let curCs' := if curCs.head? == some c then curCs else c :: curCs
      groupPre d curCs' true acc r
    else groupPre d [c] true ((curD, curCs.reverse.toArray) :: acc) r

/-- Group `(c, d)` pairs into sorted `(d, #[c₁, …])` preimage table. -/
def buildPreimages (pairs : List (Nat × Nat)) : Array (Nat × Array Nat) :=
  (groupPre 0 [] false [] (sortPairsDC pairs)).toArray

def scfPreimages : Array (Nat × Array Nat) := buildPreimages scfPairsList
def nonUCanonPreimages : Array (Nat × Array Nat) := buildPreimages nonUCanonPairsList

end Engine.Model
