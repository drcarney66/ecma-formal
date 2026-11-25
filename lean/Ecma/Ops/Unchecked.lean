module

public import Ecma.Notation.Syntax

@[expose] public section

/-!
# Unchecked Asserts

A prose Assert whose condition has no declared meaning cannot be checked: checked mode passes
over it (it is neither stopped at nor assumed): its meaning is to continue. The run's dispatch tells
its observer (`PassHook`), which leaves the state as it is. `Cond.pass` is such a condition by its key
alone.
-/

namespace Ecma

/-- An unchecked condition by its key: unchecked in every mode. -/
def Cond.unchecked : Cond → Bool
  | .pass _ => true
  | _ => false

/-- The unchecked condition of `Assert: If c, then d`: `c`'s, else `d`'s. -/
def uncheckedIf (c d : Cond) : Option Cond :=
  if c.unchecked then some c else if d.unchecked then some d else none

/-- A pass condition's key within its algorithm. -/
def Cond.proseKey : Cond → String
  | .pass k => k
  | _ => ""

end Ecma
