module

public import Engine.Proofs.Step.Sym.Basic
public import Engine.Proofs.Step.Sym.Loops
public import Engine.Proofs.Step.Sym.Prims
public import Engine.Proofs.Step.Sym.Sorts
public import Engine.Proofs.Step.Sym.Store

/-!
# Symbolic execution of the machine

What a row's proof steps the specification's machine with: the runs and the stepping tactics (`Sym/Basic`:
`mstep`, `gstep`, `gsteps`, `Steps.next`, `Steps.trans`, `Steps.valBool`), a loop's round's head (`Sym/Loops`),
a primitive's call (`Sym/Prims`), the program's algorithms and sorts (`Sym/Sorts`), the store (`Sym/Store`).
-/
