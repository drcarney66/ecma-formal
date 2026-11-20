module

public import Ecma.Grammar.Derives
public import Unicode.Gen.Classes

@[expose] public section

/-!
# Bare's code point primitives of the grammars

The (b) primitives of the code point grammars at Bare (`Ecma.Grammar.CodePrims`): the descriptive
phrases' classes (ID_Start and ID_Continue from the Unicode Character Database, `UCD`), <USP>
(Space_Separator), and the `[> but only if …]` conditions, each the MV of the node's
hexadecimal digits. B.1.2's group-number condition reads the whole Pattern's capturing groups; it
is a parameter (`group`).
-/

namespace Engine.Model

open Ecma.Grammar

/-- <USP>: General_Category Space_Separator. -/
def usp (c : Nat) : Bool := Unicode.spaceSeparator c

/-- ID_Start. -/
def idStart (c : Nat) : Bool := Unicode.idStart c

/-- ID_Continue. -/
def idContinue (c : Nat) : Bool := Unicode.idContinue c

end Engine.Model
