module

public import Ecma.Notation.Syntax

@[expose] public section

/-!
# Ecma syntax: `Repr` instances

The derived `Repr` instances of `Ecma.Ecma.Syntax`'s types, for printing and debugging.
-/

namespace Ecma

deriving instance Repr for AlgId, Attr, XrefForm, Xref, Sub, Numeral, Sign, Mag, ValLit, Article,
  AltForm, ConnForm, Conj, ListForm, UnOp, DataLit, BinOp, RelOp, MathFn, Callee, Channel, PrimDoc, Reading,
  CloKind, AlgKind, RowForm, PhraseArg, PhraseMeaning, SortDef, Phrase, GTerminal

end Ecma
