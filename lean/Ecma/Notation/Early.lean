module

public import Ecma.Notation.Syntax

@[expose] public section

/-!
# Ecma syntax: Early Errors rules as data

An Early Errors clause's rule rows: each `<li>` of the list after an
`<emu-grammar>` block, keyed by the block's productions, as its sentences.
`Print.Early` prints a row back as the content between `<li>` and `</li>`.
-/

namespace Ecma

/-- How an early-error rule writes its exception. -/
inductive UnlessForm where
  /-- ` unless c` -/
  | plain
  /-- `, unless c` -/
  | comma
  /-- ` normopt, unless c` -/
  | optional
  deriving Repr, BEq, Inhabited

/-- A sentence of an early-error rule. -/
inductive EarlySentence where
  /-- `It is a Syntax Error if c` (`early`: `It is an early Syntax Error if c`), and its exception -/
  | syntaxError (early : Bool) (c : Cond) (unless_ : Option (UnlessForm × Cond))
  /-- `It is a Syntax Error if c <ins>and d</ins>.`: Annex B's edit, applied as `c and d` -/
  | syntaxErrorIns (c d : Cond)
  /-- `p must cover t.`: `p`, a node of this production, is reparsed as `t` and checked under its rules -/
  | mustCover (p : Expr) (t : TyExpr)
  /-- `The Early Error rules for <raw> are applied.`: production `p`'s rules -/
  | rulesApplied (ps : List ProdId) (raw : String)
  /-- `If c, s` (`s` lower-cased) -/
  | ifInline (c : Cond) (s : EarlySentence)
  /-- an informative sentence (`Additional early error rules for … are defined in …`): no errors -/
  | info (s : Stmt)
  /-- `For each t x in l: It is a Syntax Error if c.` (written `s`): an error per element of `l` that is a `t` and meets `c` -/
  | forEachIn (x : Slot) (t : TyExpr) (l : Expr) (c : Cond) (s : Stmt)
  /-- `This rule is not applied if c …` (written `s`): the row gives no errors where `c` holds -/
  | notApplied (c : Cond) (s : Stmt)
  /-- any other sentence, as a statement -/
  | stmt (s : Stmt)
  deriving Inhabited

/-- An early-error rule row: one bullet of an Early Errors clause. -/
structure EarlyRow where
  /-- the clause, and the bullet's position after the clause's defs and equations -/
  id : AlgId
  /-- the SDO "Early Errors" -/
  sdo : SdoId
  prods : List ProdId
  /-- the block's grammar keys as written -/
  keys : List String
  vars : Array String
  body : List EarlySentence
  /-- an annex rule that modifies the main rules of its productions: it stands for them -/
  modifies : Bool := false
  deriving Inhabited

end Ecma
