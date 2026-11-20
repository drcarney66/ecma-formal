module

public import Ecma.Spec.Program
public import Ecma.Lower.Choice
meta import Ecma.Spec.Program
meta import Ecma.Lower.Choice

/-!
# The specification's choice sites, checked when the engine builds

The constructive functions that make the text's choices (`Ecma.Prog.expandChoice`: YearFromTime's and MakeDay's
searches) find their steps by algorithm id and by
the steps' shape. A step that no longer has that shape keeps the text's choice, which the machine cannot make,
and the program would run on without a sign of it until a run reached the step. This module does not build unless
every site is found in the specification's program (`Ecma.Prog.choiceSitesUnmatched`).
-/

#guard Ecma.Spec.src.prog.choiceSitesUnmatched.isEmpty
