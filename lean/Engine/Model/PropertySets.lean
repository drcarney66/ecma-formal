module

public import Ecma.Unicode.Gen.Properties
public import Unicode.Gen.PropertyValues
public import Unicode.Gen.PropertyValueAliases

@[expose] public section

/-!
# The CharSetElements of a Unicode property value

"The CharSetElements whose character database definition includes the property _p_ with value
_v_" (§22.2.2.9 CompileToCharSet) over the Unicode library's tables and ECMA-262's properties (`Properties.lean`):
names are code points, a property and a value each by its name or an alias (PropertyAliases.txt,
PropertyValueAliases.txt, Tables 65–67); a binary property's values are those of
PropertyValueAliases.txt's binary properties (Y, Yes, T, True; N, No, F, False).
-/

namespace Engine.Model.Unicode

open _root_.Unicode Ecma.Unicode

/-- The entry of a name table whose name is the code points `n`. -/
def find? {α : Type} (n : List Nat) : List (String × α) → Option α
  | [] => none
  | (k, a) :: r => if k.toList.map Char.toNat = n then some a else find? n r

/-- The names of a binary property's value True. -/
def trueNames : List String := ["Y", "Yes", "T", "True"]

/-- The names of a binary property's value False. -/
def falseNames : List String := ["N", "No", "F", "False"]

/-- Whether `n` is one of the names. -/
def named (n : List Nat) (ks : List String) : Bool := ks.any fun k => k.toList.map Char.toNat = n

/-- The code points 0 to 0x10FFFF that no range covers, for ranges sorted by first element. -/
def gaps (rs : List (Nat × Nat)) : List (Nat × Nat) :=
  let r := rs.foldl (fun (acc : List (Nat × Nat) × Nat) (x : Nat × Nat) =>
    (if acc.2 < x.1 then (acc.2, x.1 - 1) :: acc.1 else acc.1, max acc.2 (x.2 + 1))) ([], 0)
  (if r.2 ≤ 0x10FFFF then (r.2, 0x10FFFF) :: r.1 else r.1).reverse

/-- The property value's elements: its code points as ranges, and its sequences of two or more
code points; `none` where `p`, `v` name no property value, or one with infinitely many elements
(the value False of a property of strings). -/
def propertyValue? (p v : List Nat) : Option (List (Nat × Nat) × List (List Nat)) :=
  match find? p nonBinaryPropertyNames with
  | some .«General_Category» => (find? v GeneralCategory.valueAliases).map fun x => (x.codePoints, [])
  | some .«Script» => (find? v Script.valueAliases).map fun x => (x.codePoints, [])
  | some .«Script_Extensions» => (find? v Script.valueAliases).map fun x => (x.extensionsCodePoints, [])
  | none =>
    match find? p binaryPropertyNames with
    | some b =>
      if named v trueNames then some (b.codePoints, [])
      else if named v falseNames then some (gaps (b.codePoints.mergeSort fun x y => x.1 ≤ y.1), [])
      else none
    | none =>
      match find? p stringPropertyNames with
      | some s => if named v trueNames then some s.elements else none
      | none => none

/-- The words of a row of names separated by spaces, as code points. -/
def rowNames (r : String) : List (List Nat) :=
  (r.toList.splitOn ' ').map (·.map Char.toNat)

/-- The long name of the value `v` names for the property `p` names (PropertyValueAliases.txt,
names compared exactly); `none` where `p` names no property or `v` none of its values. -/
def propertyValueName? (p v : List Nat) : Option (List Nat) := do
  let ns ← ucdPropertyNames.find? fun ns => named p ns
  let short ← ns.head?
  let rows ← find? (short.toList.map Char.toNat) ucdPropertyValueRows
  let r ← rows.find? fun r => (rowNames r).contains v
  (rowNames r).head?

end Engine.Model.Unicode
