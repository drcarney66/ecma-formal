module

public import Engine.Model.PropertySets

@[expose] public section

/-!
# A property value's CharSetElements, checked

The instances' `Model.propSet`: `Engine.Model.Unicode.propertyValue?`'s ranges and sequences, sorted and checked
(ranges disjoint and within the code points, sequences of two or more code points with
increasing keys), then each code point as a sequence of one. The checks make the elements
distinct sequences of characters (`elements_wf`), which `Model.UnicodeLaws` asks for.
-/

namespace Engine.PropSets

/-- Each range within the code points and below the next. -/
def rangesOk : List (Nat × Nat) → Bool
  | [] => true
  | [(a, b)] => a ≤ b && b ≤ 0x10FFFF
  | (a, b) :: (c, d) :: r => a ≤ b && b < c && rangesOk ((c, d) :: r)

/-- The code points of the ranges. -/
def expand (rs : List (Nat × Nat)) : List Nat := rs.flatMap fun x => List.range' x.1 (x.2 + 1 - x.1)

/-- A sort key of a sequence of code points. -/
def key (s : List Nat) : Nat := s.foldl (fun k c => k * 0x110001 + c + 1) 0

/-- Each sequence of two or more code points, and its key below the next one's. -/
def stringsOk : List (List Nat) → Bool
  | [] => true
  | s :: r => 2 ≤ s.length && s.all (· ≤ 0x10FFFF) &&
      (match r with | [] => true | t :: _ => key s < key t) && stringsOk r

/-- The CharSetElements, as sequences of code points, of the property value `p`, `v` names;
`none` where `Engine.Model.Unicode.propertyValue?` has none or a check fails. -/
def elements (p v : List Nat) : Option (List (List Nat)) := do
  let (rs, ss) ← Engine.Model.Unicode.propertyValue? p v
  let rs := rs.mergeSort fun x y => x.1 ≤ y.1
  let ss := ss.mergeSort fun x y => key x ≤ key y
  if rangesOk rs && stringsOk ss then some ((expand rs).map ([·]) ++ ss) else none

end Engine.PropSets
