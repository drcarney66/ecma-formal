module

public import Ecma.Grammar.Gen.Symbols

@[expose] public section

/-!
# The grammar notation (ECMA-262 §5.1.6) as data

The grammars of spec.html (the lexical, syntactic, RegExp and numeric string
grammars, the supplemental grammars and Annex B's) are generated as values of
these types by `crates/jsgrammar` (`Grammar/Gen/*`, constructor and `List` data
only), and `Grammar/Print.lean` prints them back in spec.html's notation
(docs/parser/GRAMMAR.md). Each constructor is one form of §5.1.6's notation
(or §5.1.1's colons); its docstring says which. What the notation means, a
derivation relation over these values, is `Grammar.Derives`.

The nonterminals and the parameters are the enumerations `NT` and `Param` of
`Gen/Symbols.lean`, generated from the same blocks.
-/

namespace Ecma.Grammar

/-- A nonterminal's name, as spec.html writes it. -/
def NT.name (n : NT) : String := NT.names.getD n.ctorIdx "?"

/-- A parameter's name, as spec.html writes it. -/
def Param.name (p : Param) : String := Param.names.getD p.ctorIdx "?"

instance : Repr NT := ⟨fun n _ => .text ("." ++ n.name)⟩
instance : Repr Param := ⟨fun p _ => .text ("." ++ p.name)⟩

/-- §5.1.1, §5.1.3, §5.1.4 and §5.2.4: the grammar a production belongs to, by
its colons: `:` the syntactic grammar, `::` the lexical and RegExp grammars,
`:::` the numeric string grammar. -/
inductive Colons where
  | one
  | two
  | three
  deriving Repr, BEq, Inhabited

/-- §5.1.6 "Grammatical Parameters": how a reference sets a parameter: `+P` (set),
`~P` (not set), `?P` (as the referring production's own). -/
inductive Sign where
  | plus
  | tilde
  | quest
  deriving Repr, BEq, Inhabited

/-- A parameter argument of a nonterminal reference, `Name[+In, ?Yield]`. -/
structure Arg where
  sign : Sign
  param : Param
  deriving Repr, BEq, Inhabited

/-- The code points written `<NAME>` (§12.2 Table 34, §12.3 Table 35). -/
inductive CodePointName where
  | TAB
  | VT
  | FF
  | ZWNBSP
  | USP
  | LF
  | CR
  | LS
  | PS
  deriving Repr, BEq, Inhabited

/-- The code point a name stands for (§12.2 Table 34, §12.3 Table 35), or none
for `<USP>`, the class "any code point in general category “Space_Separator”",
a declared primitive of the machine. -/
def CodePointName.codePoint : CodePointName → Option Nat
  | .TAB => some 0x0009
  | .VT => some 0x000B
  | .FF => some 0x000C
  | .ZWNBSP => some 0xFEFF
  | .USP => none
  | .LF => some 0x000A
  | .CR => some 0x000D
  | .LS => some 0x2028
  | .PS => some 0x2029

/-- A terminal symbol (§5.1.6): a code point sequence written in a fixed-width
font (`` `if` ``; in spec.html between backticks), or a code point by name. -/
inductive Terminal where
  /-- `alt`: spec.html spells it the other way (`Terminal.render`), which the
  derivation relation ignores. -/
  | text (s : String) (alt : Bool)
  | cp (n : CodePointName)
  deriving Repr, BEq, Inhabited

/-- A grammar symbol: a terminal, or a nonterminal with its parameter arguments. -/
inductive Sym where
  | t (x : Terminal)
  | nt (n : NT) (args : List Arg)
  deriving Repr, BEq, Inhabited

/-- An element of a lookahead token sequence: a terminal, or (in a lookahead
sequence of the syntactic grammar) `[no LineTerminator here]`. -/
inductive LookItem where
  | t (x : Terminal)
  | noLT
  deriving Repr, BEq, Inhabited

/-- §5.1.6 "Lookahead restrictions": `[lookahead = seq]` (written `==`),
`[lookahead ≠ seq]` (written `!=`), `[lookahead ∈ set]`, `[lookahead ∉ set]`
with a set of sequences in braces, and `[lookahead ∉ N]` with a nonterminal
whose language is a finite set of terminals. -/
inductive Lookahead where
  | eq (seq : List LookItem)
  | ne (seq : List LookItem)
  | mem (seqs : List (List LookItem))
  | notMem (seqs : List (List LookItem))
  | notMemNT (n : NT)
  deriving Repr, BEq, Inhabited

/-- §5.1.6 "but not": what follows `but not`: one symbol, or `one of` a list,
separated by `or` (`orSep := true`) or by spaces. -/
inductive Exclusion where
  | sym (s : Sym)
  | oneOf (syms : List Sym) (orSep : Bool)
  deriving Repr, BEq, Inhabited

/-- §5.1.6: the descriptive phrases (a right-hand side `> …` where listing all
alternatives would be impractical), and the conditions of `[> but only if …]`.
Their meaning is given by hand with the kernel (P1); the printer prints their
spec.html text. -/
inductive Phrase where
  /-- `> any Unicode code point` (§11.1, SourceCharacter) -/
  | anyCodePoint
  /-- `> any Unicode code point with the Unicode property “ID_Start”` (§12.7) -/
  | idStart
  /-- `> any Unicode code point with the Unicode property “ID_Continue”` (§12.7) -/
  | idContinue
  /-- `> any Unicode code point in the inclusive interval from U+D800 to U+DBFF` (§22.2.1) -/
  | leadSurrogate
  /-- `> any Unicode code point in the inclusive interval from U+DC00 to U+DFFF` (§22.2.1) -/
  | trailSurrogate
  /-- `but only if the MV of |HexDigits| > 0x10FFFF` (§12.9.4, NotCodePoint) -/
  | mvAbove10FFFF
  /-- `but only if the MV of |HexDigits| ≤ 0x10FFFF` (§12.9.4, CodePoint) -/
  | mvAtMost10FFFF
  /-- `but only if the MV of |Hex4Digits| is in the inclusive interval from 0xD800 to 0xDBFF` (§22.2.1) -/
  | mvLead
  /-- `but only if the MV of |Hex4Digits| is in the inclusive interval from 0xDC00 to 0xDFFF` (§22.2.1) -/
  | mvTrail
  /-- `but only if the MV of |Hex4Digits| is not in the inclusive interval from 0xD800 to 0xDFFF` (§22.2.1) -/
  | mvNonSurrogate
  /-- `but only if the CapturingGroupNumber of |DecimalEscape| is ≤ CountLeftCapturingParensWithin(the |Pattern| containing |DecimalEscape|)` (B.1.2) -/
  | groupNumberAtMostCount
  deriving Repr, BEq, Inhabited

/-- One element of a right-hand side (§5.1.6). -/
inductive Item where
  /-- A symbol, optional when written with the `opt` subscript (`?` in spec.html). -/
  | sym (s : Sym) (opt : Bool)
  /-- A lookahead restriction. -/
  | lookahead (l : Lookahead)
  /-- `[no LineTerminator here]`. -/
  | noLT
  /-- `[empty]`: the right-hand side derives no terminals. -/
  | empty
  /-- `base but not …`: an instance of `base` that is not one of the excluded. -/
  | butNot (base : Sym) (ex : Exclusion)
  /-- `[> but only if …]`: a condition on the item before it. -/
  | onlyIf (c : Phrase)
  /-- `> …`: a descriptive phrase, the whole right-hand side. -/
  | phrase (p : Phrase)
  deriving Repr, BEq, Inhabited

/-- One condition of a guard `[+P]`, `[~P]` or `[+P, ~Q]` before a right-hand
side (§5.1.6): the alternative exists only when every condition holds, the
parameter set (`plus := true`) or not. -/
structure Guard where
  plus : Bool
  param : Param
  deriving Repr, BEq, Inhabited

/-- One alternative: its guard (no conditions when it has none), its right-hand
side and its `#label`. -/
structure Alt where
  guard : List Guard
  rhs : List Item
  label : Option String
  deriving Repr, BEq, Inhabited

/-- The alternative without its lookahead restrictions. -/
def Alt.bare (a : Alt) : Alt := { a with rhs := a.rhs.filter fun | .lookahead _ => false | _ => true }

/-- A definition's alternatives, or `one of` (§5.1.6) with its rows of terminals,
each terminal an alternative. -/
inductive Body where
  | alts (as : List Alt)
  | oneOf (rows : List (List Terminal))
  deriving Repr, BEq, Inhabited

/-- One definition of a nonterminal: `Lhs[Params] : alternatives`. -/
structure Rule where
  lhs : NT
  params : List Param
  colons : Colons
  body : Body
  deriving Repr, BEq, Inhabited

/-- The grammars, in GL's order (`prodsOf`): the numeric string, lexical,
syntactic (with its supplemental grammars), RegExp grammars, Annex B's
overlays, and json.emu's JSON grammar. -/
inductive GrammarId where
  | numericString
  | lexical
  | syntactic
  | regExp
  | annexB
  | json
  deriving Repr, BEq, Inhabited

/-! ## Right-hand sides

The order of right-hand sides (§5.1.6, "Optional Symbols": an alternative with
`k` optional symbols specifies `2^k` right-hand sides): grammar by grammar,
then by written production (a rule's alternatives, or its `one of` terminals,
in spec order), then over the presences of its optional symbols, absent
before present, the first the most significant. A right-hand side's
production id is not its place in this order but the number
spec/formal/prod-ids.txt gives it (`prodsById`): a right-hand side keeps its
number when others are added or removed. -/

/-- One right-hand side: a written production of a grammar and the presence of
each of its optional symbols. -/
structure Prod where
  grammar : GrammarId
  rule : Rule
  /-- its index among the rule's alternatives, or its `one of` terminals -/
  alt : Nat
  /-- its written production's index in its grammar (its `Production` constructor) -/
  ctor : Nat
  mask : List Bool
  deriving Repr, BEq, Inhabited

/-- The number of optional symbols of an alternative. -/
def Alt.opts (a : Alt) : Nat := (a.rhs.filter fun | .sym _ true => true | _ => false).length

/-- The presence masks of `k` optional symbols, in id order. -/
def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (masks n).map (false :: ·) ++ (masks n).map (true :: ·)

/-- A rule's written productions: the number of optional symbols of each. -/
def Rule.written (r : Rule) : List Nat :=
  match r.body with
  | .alts as => as.map Alt.opts
  | .oneOf rows => rows.flatten.map fun _ => 0

/-- The right-hand sides of `gs`, in id order. -/
def prodsOf (gs : List (GrammarId × List Rule)) : List Prod :=
  gs.flatMap fun (g, rules) =>
    let ws := rules.flatMap fun r => r.written.zipIdx.map fun (k, i) => (r, i, k)
    ws.zipIdx.flatMap fun ((r, i, k), c) => (masks k).map fun m => ⟨g, r, i, c, m⟩

/-- The numbers of runs `(a, n)`: `a`, `a + 1`, …, `a + n - 1`, run by run. -/
def idsOfRuns (rs : List (Nat × Nat)) : List Nat := rs.flatMap fun (a, n) => List.range' a n

/-- The right-hand sides of `gs` by production id: `ids` (as runs) gives each of `prodsOf gs`, in order,
its number, and entry `n` of the `next` entries is the right-hand side numbered `n`; none at a number no
right-hand side has (a retired production's). -/
def prodsById (gs : List (GrammarId × List Rule)) (ids : List (Nat × Nat)) (next : Nat) : Array (Option Prod) :=
  let numbered := (prodsOf gs).zip (idsOfRuns ids)
  ((List.range' 0 next).map fun n => (numbered.find? (·.2 == n)).map (·.1)).toArray

/-- A written production's alternative (none for a `one of` terminal). -/
def Prod.altOf (p : Prod) : Option Alt :=
  match p.rule.body with
  | .alts as => as[p.alt]?
  | .oneOf _ => none

/-- A reading of a rule: the definition of `rule.lhs` in `grammar` under the
reading, replacing the pinned one: an erratum's (`erratum` indexes the errata),
or with none an interpreting reading, in effect under every reading of the errata. -/
structure RuleReading where
  erratum : Option Nat
  grammar : GrammarId
  rule : Rule
  deriving Repr, BEq, Inhabited

/-- The Annex B sections whose grammar is an overlay of the main grammar, by
clause id: B.1.1 `sec-html-like-comments`, B.1.2
`sec-regular-expressions-patterns`, B.3.3
`sec-functiondeclarations-in-ifstatement-statement-clauses` and B.3.5
`sec-initializers-in-forin-statement-heads`. -/
inductive AnnexB where
  | htmlLikeComments
  | regExpPatterns
  | functionDeclarationsInIfStatement
  | initializersInForIn
  deriving Repr, BEq, Inhabited

/-- An Annex B section's clause id. -/
def AnnexB.clause : AnnexB → String
  | .htmlLikeComments => "sec-html-like-comments"
  | .regExpPatterns => "sec-regular-expressions-patterns"
  | .functionDeclarationsInIfStatement => "sec-functiondeclarations-in-ifstatement-statement-clauses"
  | .initializersInForIn => "sec-initializers-in-forin-statement-heads"

/-- A set of Annex B sections (the ones a host supports), one membership bit per section. -/
structure AnnexB.Set where
  html : Bool := false
  regExp : Bool := false
  ifFunctions : Bool := false
  forInInit : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Whether section `s` is in the set. -/
def AnnexB.Set.has (S : AnnexB.Set) : AnnexB → Bool
  | .htmlLikeComments => S.html
  | .regExpPatterns => S.regExp
  | .functionDeclarationsInIfStatement => S.ifFunctions
  | .initializersInForIn => S.forInInit

/-- Whether any section is in the set. -/
def AnnexB.Set.any (S : AnnexB.Set) : Bool := S.html || S.regExp || S.ifFunctions || S.forInInit

/-- How an overlay's rules combine with the main grammar's definitions of the
same nonterminals, as its section says: `extend` (B.1.1 "is extended as
follows", B.3.3 and B.3.5 "augments") is the union of the main definition's
alternatives and the overlay's, an alternative the overlay restates (equal as
an `Alt`) counted once: B.1.1 restates whole definitions (its
`InputElementHashbangOrRegExp` repeats the main one's six alternatives and adds
`HTMLCloseComment`), and a restated alternative is not a second production.
The report lists the restated alternatives (`@@restated`,
tests/parser/grammar_index.txt). `replace` is B.1.2's "is modified and
extended as follows … each alternative is considered only if previous
production alternatives do not match": the overlay's definition, in its
order, replaces the main one. -/
inductive OverlayMode where
  | extend
  | replace
  deriving Repr, BEq, Inhabited

/-- When an Annex B overlay applies, as its section's prose says (checked by the
generator, which fails when the prose changes): `always` (B.1.2), `notModule`
(B.1.1: "this extension is not allowed when parsing source text using the
goal symbol |Module|"), `nonStrict` (B.3.3 and B.3.5: "This production only
applies when parsing non-strict code"). So the grammar a parse uses depends
on the goal and on strictness, besides which Annex B sections the host
supports. -/
inductive OverlayCond where
  | always
  | notModule
  | nonStrict
  deriving Repr, BEq, Inhabited

/-- What a definition block is: of the main grammar, a supplemental grammar
(§5.1.5: "the interpretation of |cover| is refined using the following
grammar"), or an Annex B overlay with its mode and its condition. -/
inductive BlockKind where
  | main
  | supplemental (cover : NT)
  | overlay (sec : AnnexB) (mode : OverlayMode) (cond : OverlayCond)
  deriving Repr, BEq, Inhabited

/-- One `<emu-grammar type="definition">` block of spec.html: its clause id, the
line of its opening tag, its kind and its rules in order. -/
structure Block where
  clause : String
  line : Nat
  kind : BlockKind
  rules : List Rule
  /-- the indentation of its rules -/
  indent : Nat
  /-- the rules a `// emu-format ignore` line precedes, by index -/
  fmtIgnore : List Nat
  deriving Repr

/-- How spec.html names a goal symbol. -/
inductive GoalSrc where
  /-- §5.1: "starting from the goal symbol |X|" (or "two alternative goal symbols") -/
  | grammar
  /-- "ParseText(_s_, |X|)" -/
  | parseText
  /-- CreateDynamicFunction: "be the grammar symbol |X|" -/
  | grammarSymbol
  /-- "must have the syntax of a |X|" -/
  | syntaxOf
  /-- an early error's "must cover a |X|" -/
  | mustCover
  /-- the first definition of a supplemental block -/
  | supplemental
  /-- a supplemental grammar given as a copy of its definition -/
  | copy
  /-- json.emu: "its goal symbol is |X|" (the line is json.emu's) -/
  | json
  deriving Repr, BEq, Inhabited

/-- A goal symbol instance (§5.1.1–§5.1.5, ParseText's callers), with the
spec.html line it is named on and how. -/
structure Goal where
  nt : NT
  args : List Arg
  line : Nat
  src : GoalSrc
  deriving Repr

/-- A supplemental-grammar cover (§5.1.5): when processing an instance of
production `context` (of the syntactic grammar's `Production` type `P`), "the
interpretation of |cover| is refined using the following grammar", with goal
`refined` (the supplemental block, or the copy of a definition, at `line`).
These are only the sites whose prose says "is refined using the following
grammar". The early errors' "must cover" sites are not here (for example
DestructuringAssignmentTarget : LeftHandSideExpression, spec.html:21512, and
the LeftHandSideExpression of the for-in, for-of and for-await-of heads,
spec.html:22780): they come with the static semantics (`Static/Cover`, P5a). -/
structure Cover (P : Type) where
  context : P
  cover : NT
  refined : NT
  line : Nat
  deriving Repr

/-- §12.10 "Rules of Automatic Semicolon Insertion": where a `;` of the
syntactic grammar's right-hand sides may be a virtual (inserted) one. -/
inductive Semi where
  /-- Rules 1–3 may insert it. -/
  | insertable
  /-- Insertable by rules 1–3, as `insertable` (an offending token after a
  LineTerminator, `}`, or the end of input), and also by rule 1's special
  case: "the previous token is ) and the inserted semicolon would then be
  parsed as the terminating semicolon of a do-while statement (14.7.2)". -/
  | doWhile
  /-- Never: "if the semicolon would then be parsed as an empty statement". -/
  | emptyStatement
  /-- Never: "if that semicolon would become one of the two semicolons in the
  header of a for statement (see 14.7.4)". -/
  | forHeader
  /-- Insertable, except where this production ends the |LexicalDeclaration| of
  `for ( LexicalDeclaration Expression? ; …`, where the `;` is the header's
  first: there it is `forHeader`. -/
  | forHeaderIfDeclaration
  deriving Repr, BEq, Inhabited

/-- The `;` at right-hand side position `pos` (counting the items of
`Alt.rhs` from 0) of production `prod`, and §12.10's answer for it. -/
structure SemiSite (P : Type) where
  prod : P
  pos : Nat
  semi : Semi
  deriving Repr

end Ecma.Grammar
