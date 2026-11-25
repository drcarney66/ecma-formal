module

public import Ecma.Notation.Syntax

@[expose] public section

/-!
# Ecma syntax: `Repr` instances

The derived `Repr` instances of `Ecma.Ecma.Syntax`'s types, for printing and debugging.
-/

namespace Ecma

deriving instance Repr for AlgId, Sub, Numeral, Sign, Mag, ValLit, Conj, UnOp, DataLit, BinOp, RelOp,
  MathFn, Callee, PrimDoc, CloKind, AlgKind, RowForm, SortArg, SortTest, SortDef, GTerminal

end Ecma
