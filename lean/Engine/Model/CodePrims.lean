module

public import Ecma.Grammar.Derives
public import Unicode.Gen.Classes

@[expose] public section

/-!
# Bare's code point primitives of the grammars

The (b) primitives of the code point grammars at Bare (`Ecma.Grammar.CodePrims`): the descriptive
phrases' classes (ID_Start and ID_Continue from the Unicode Character Database, `UCD`), `<USP>`
(Space_Separator), and the `[> but only if …]` conditions, each the MV of the node's
hexadecimal digits (`Grammar.hexMV`). B.1.2's group-number condition reads the whole Pattern's
capturing groups through `CodePrims.withGroup`.
-/

namespace Engine.Model

open Ecma.Grammar

/-- <USP>: General_Category Space_Separator. -/
def usp (c : Nat) : Bool := Unicode.spaceSeparator c

/-- ID_Start. -/
def idStart (c : Nat) : Bool := Unicode.idStart c

/-- ID_Continue. -/
def idContinue (c : Nat) : Bool := Unicode.idContinue c

/-- Bare's (b) primitives of the code point grammars (`Ecma.Grammar.CodePrims`). -/
def codePrims : CodePrims where
  phrase p c := match p with
    | .anyCodePoint => c ≤ 0x10FFFF
    | .idStart => idStart c = true
    | .idContinue => idContinue c = true
    | .leadSurrogate => 0xD800 ≤ c ∧ c ≤ 0xDBFF
    | .trailSurrogate => 0xDC00 ≤ c ∧ c ≤ 0xDFFF
    | _ => False
  usp c := usp c = true
  cond p inp t :=
    let s := slice inp t.span.1 t.span.2
    match p with
    | .mvAbove10FFFF => ∃ v, hexMV s = some v ∧ 0x10FFFF < v
    | .mvAtMost10FFFF => ∃ v, hexMV s = some v ∧ v ≤ 0x10FFFF
    | .mvLead => ∃ v, hexMV s = some v ∧ 0xD800 ≤ v ∧ v ≤ 0xDBFF
    | .mvTrail => ∃ v, hexMV s = some v ∧ 0xDC00 ≤ v ∧ v ≤ 0xDFFF
    | .mvNonSurrogate => ∃ v, hexMV s = some v ∧ ¬ (0xD800 ≤ v ∧ v ≤ 0xDFFF)
    | _ => False

end Engine.Model
