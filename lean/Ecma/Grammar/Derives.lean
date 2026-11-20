module

public import Ecma.Grammar.Notation

@[expose] public section

/-!
# What ECMA-262's grammar notation means (§5.1)

`Derives` is §5.1's derivation relation over GL's notation (`Grammar.Core`,
read through `Grammar.Notation`),
for each grammar and goal symbol, with parameters and guards (§5.1.6),
optional symbols (one right-hand side per presence mask, so a node's
production is a GL production id), lookahead, `[no LineTerminator here]`,
`but not` and `[empty]`. Its terminals come from an `Alphabet`: code points for
the lexical, RegExp and numeric string grammars, tokens for the syntactic
grammar. The descriptive phrases, `<USP>` and the `[> but only if …]`
conditions are the alphabet's (b) primitives.

`but not` and the lookahead `∉ N` are negative. `Derives` is therefore the
limit of strata: stratum `k + 1` reads the exclusions in stratum `k`, and a
derivation is one at every stratum from some on, which is §5.1's relation for
a grammar whose exclusions are stratified, as GL's are.

The rest of §5.1.3, §5.1.5, §11 and §12 is stated over it: scanning source
text into input elements (`Scans`), the tokens and their line terminators,
the choice of lexical goal at the parse's position (`GoalsAt`), automatic semicolon insertion
(`ASIOk`), and chain productions (`chainNt`).
-/

namespace Ecma.Grammar

/-! ## Derivations -/

/-- A Parse Node: a nonterminal instance with its production id, its
parameters and its span of the input; a leaf (a terminal or a phrase) and its
span; or input element `k` as an instance of another grammar's nonterminal,
with that grammar's derivation `t` over the element's code points. -/
inductive Tree where
  | leaf (i j : Nat)
  | node (n : NT) (id : Nat) (ps : List Param) (i j : Nat) (kids : List Tree)
  | lex (k : Nat) (t : Tree)

/-- A node of nonterminal `n` spanning `i` to `j` is in the tree. -/
def Tree.has (n : NT) (i j : Nat) : Tree → Bool
  | .node m _ _ a b kids => (m == n && a == i && b == j) || kids.attach.any fun ⟨k, _⟩ => k.has n i j
  | .leaf .. => false
  | .lex _ t => t.has n i j

/-- A terminal's tree: no Parse Node child of its parent. -/
def Tree.isLeaf : Tree → Bool
  | .leaf .. => true
  | _ => false

def Tree.nt? : Tree → Option NT
  | .node n .. => some n
  | .leaf .. => none
  | .lex _ t => t.nt?

def Tree.span : Tree → Nat × Nat
  | .leaf i j => (i, j)
  | .lex k _ => (k, k + 1)
  | .node _ _ _ i j _ => (i, j)

/-- The elements `i` to `j` of the input. -/
def slice {T : Type} (inp : List T) (i j : Nat) : List T := (inp.drop i).take (j - i)

/-- A grammar's terminals. -/
structure Alphabet (T : Type) where
  /-- terminal `x`, at item `k` of right-hand side `s`, matches these input elements -/
  term : Src → Nat → Terminal → List T → Prop
  /-- (b) a descriptive phrase's class -/
  phrase : Phrase → List T → Prop
  /-- (b) a `[> but only if …]` condition on the node derived for the item
  before it, in the whole input -/
  cond : Phrase → List T → Tree → Prop
  /-- this input element is an instance of a nonterminal this grammar does not
  define, derived as `t` over its code points -/
  leaf : NT → T → Tree → Prop
  /-- no line terminator before the input element at this position -/
  noLT : List T → Nat → Prop
  /-- the position a lookahead reads from this one: past the elements §12.10 inserted -/
  look : List T → Nat → Nat := fun _ j => j

section
variable {T : Type} (A : Alphabet T) (neg : NT → List Param → Nat → Nat → Prop) (inp : List T)

/-- The input from `j` starts with the lookahead sequence, each item read from `A.look`. -/
def StartsWith (s : Src) : List LookItem → Nat → Prop
  | [], _ => True
  | .t x :: rest, j => ∃ h, A.look inp j < h ∧ h ≤ inp.length ∧ A.term s 0 x (slice inp (A.look inp j) h) ∧
      StartsWith s rest h
  | .noLT :: rest, j => A.noLT inp (A.look inp j) ∧ StartsWith s rest j

/-- A lookahead restriction holds at `j`; `∉ N` reads `N` in `neg`. -/
def LookOk (s : Src) : Lookahead → Nat → Prop
  | .eq q, j => StartsWith A inp s q j
  | .ne q, j => ¬ StartsWith A inp s q j
  | .mem qs, j => ∃ q ∈ qs, StartsWith A inp s q j
  | .notMem qs, j => ∀ q ∈ qs, ¬ StartsWith A inp s q j
  | .notMemNT n, j => ¬ ∃ h, neg n [] j h

/-- The input `i` to `h` is an excluded symbol (in `neg` for a nonterminal). -/
def Excluded (s : Src) (k : Nat) (ps : List Param) (i h : Nat) : Exclusion → Prop
  | .sym y => match y with
    | .t x => A.term s k x (slice inp i h)
    | .nt n args => neg n (applyArgs ps args) i h
  | .oneOf ys _ => ∃ y ∈ ys, match y with
    | .t x => A.term s k x (slice inp i h)
    | .nt n args => neg n (applyArgs ps args) i h

/-- The condition after an item, if any, holds of its node. -/
def CondOk (is : List Item) (t : Tree) : Prop :=
  match is with
  | .onlyIf c :: _ => A.cond c inp t
  | _ => True

variable (gl : GL) (rd : List RuleReading) (cx : Ctx) (g : GrammarId)

mutual
/-- One stratum: nonterminal `n` with parameters `ps` derives the input `i` to
`j` as node `t`, the exclusions read in `neg`. -/
inductive Step : NT → List Param → Nat → Nat → Tree → Prop
  | node {n ps i j m kids id} (s : Src) :
      s ∈ gl.alts rd cx g n → s.alt.guard.all (Guard.holds ps) →
      gl.prodId rd s m = some id → Seq s ps 0 s.alt.rhs i j m kids →
      Step n ps i j (.node n id ps i j kids)
  | lex {n ps i t} {e : T} :
      gl.alts rd cx g n = [] → inp[i]? = some e → A.leaf n e t → Step n ps i (i + 1) (.lex i t)

/-- Items `k` on of right-hand side `s` derive the input `i` to `j`, with the
optional symbols' presences `m` and the nodes `ts`. -/
inductive Seq : Src → List Param → Nat → List Item → Nat → Nat → List Bool → List Tree → Prop
  | nil {s ps k i} : Seq s ps k [] i i [] []
  | absent {s ps k x is i j m ts} :
      Seq s ps (k + 1) is i j m ts → Seq s ps k (.sym x true :: is) i j (false :: m) ts
  | term {s ps k x o is i h j m ts} :
      A.term s k x (slice inp i h) → Seq s ps (k + 1) is h j m ts →
      Seq s ps k (.sym (.t x) o :: is) i j (if o then true :: m else m) (.leaf i h :: ts)
  | nt {s ps k n args o is i h j m t ts} :
      Step n (applyArgs ps args) i h t → CondOk A inp is t → Seq s ps (k + 1) is h j m ts →
      Seq s ps k (.sym (.nt n args) o :: is) i j (if o then true :: m else m) (t :: ts)
  | butNotT {s ps k x ex is i h j m ts} :
      A.term s k x (slice inp i h) → ¬ Excluded A neg inp s k ps i h ex → Seq s ps (k + 1) is h j m ts →
      Seq s ps k (.butNot (.t x) ex :: is) i j m (.leaf i h :: ts)
  | butNotN {s ps k n args ex is i h j m t ts} :
      Step n (applyArgs ps args) i h t → ¬ Excluded A neg inp s k ps i h ex → Seq s ps (k + 1) is h j m ts →
      Seq s ps k (.butNot (.nt n args) ex :: is) i j m (t :: ts)
  | phrase {s ps k p is i h j m ts} :
      A.phrase p (slice inp i h) → Seq s ps (k + 1) is h j m ts →
      Seq s ps k (.phrase p :: is) i j m (.leaf i h :: ts)
  | look {s ps k l is i j m ts} :
      LookOk A neg inp s l i → Seq s ps (k + 1) is i j m ts → Seq s ps k (.lookahead l :: is) i j m ts
  | noLT {s ps k is i j m ts} :
      A.noLT inp i → Seq s ps (k + 1) is i j m ts → Seq s ps k (.noLT :: is) i j m ts
  | empty {s ps k is i j m ts} :
      Seq s ps (k + 1) is i j m ts → Seq s ps k (.empty :: is) i j m ts
  | onlyIf {s ps k c is i j m ts} :
      Seq s ps (k + 1) is i j m ts → Seq s ps k (.onlyIf c :: is) i j m ts
end

end

/-- Stratum `k` of the derivation relation. -/
def DerivesAt (gl : GL) (rd : List RuleReading) (cx : Ctx) (g : GrammarId) {T : Type} (A : Alphabet T)
    (inp : List T) : Nat → NT → List Param → Nat → Nat → Tree → Prop
  | 0 => fun _ _ _ _ _ => False
  | k + 1 => Step A (fun n ps i j => ∃ t, DerivesAt gl rd cx g A inp k n ps i j t) inp gl rd cx g

/-- §5.1: in grammar `g` under reading `rd` and context `cx`, `n` with
parameters `ps` derives the input `i` to `j` as `t`: at every stratum from
some on. -/
def Derives (gl : GL) (rd : List RuleReading) (cx : Ctx) (g : GrammarId) {T : Type} (A : Alphabet T)
    (inp : List T) (n : NT) (ps : List Param) (i j : Nat) (t : Tree) : Prop :=
  ∃ K, ∀ k, K ≤ k → DerivesAt gl rd cx g A inp k n ps i j t

/-! ## Code points: the lexical, RegExp and numeric string grammars -/

/-- The (b) primitives of the code point grammars: the descriptive phrases'
classes, `<USP>`, and the `[> but only if …]` conditions (each reads a static
semantics of the node before it, which the Ecma program supplies). -/
structure CodePrims where
  phrase : Phrase → Nat → Prop
  usp : Nat → Prop
  cond : Phrase → List Nat → Tree → Prop

def codeAlphabet (P : CodePrims) : Alphabet Nat where
  term _ _ x w := match x with
    | .text s _ => w = s.toList.map Char.toNat
    | .cp n => match n.codePoint with
      | some v => w = [v]
      | none => ∃ c, w = [c] ∧ P.usp c
  phrase p w := ∃ c, w = [c] ∧ P.phrase p c
  cond := P.cond
  leaf _ _ _ := False
  noLT _ _ := True

/-- §12.3: the line terminator code points. -/
def lineTerminators : List Nat := ([.LF, .CR, .LS, .PS] : List CodePointName).filterMap CodePointName.codePoint

/-! ## Source text, input elements and tokens (§5.1.3, §11, §12) -/

/-- An input element: its span of the source text, the lexical goal it was
read with, and its derivation. -/
structure Element where
  i : Nat
  j : Nat
  goal : NT
  tree : Tree

/-- What the element is an instance of, under its goal (`WhiteSpace`,
`Comment`, `CommonToken`, …). -/
def Element.kind (e : Element) : Option NT :=
  match e.tree with
  | .node _ _ _ _ _ [k] => k.nt?
  | _ => none

/-- §5.1.3: white space, line terminators and comments are not tokens; B.1.1's |HTMLCloseComment|
is a comment. -/
def Element.isToken (e : Element) : Bool :=
  !([NT.WhiteSpace, .LineTerminator, .Comment, .HashbangComment, .HTMLCloseComment].any (some · == e.kind))

/-- §12.4, B.1.1: a line terminator, or a comment that contains a line
terminator code point (a |MultiLineComment| with one, a
|SingleLineHTMLCloseComment|), is a |LineTerminator| for the syntactic grammar. -/
def Element.breaks (src : List Nat) (e : Element) : Bool :=
  e.kind == some .LineTerminator ||
    (e.kind == some .Comment && (slice src e.i e.j).any lineTerminators.contains)

variable (gl : GL) (rd : List RuleReading) (cx : Ctx) (P : CodePrims)

/-- §12: the source text is scanned left to right into the input elements
`els`, each the longest sequence of code points its lexical goal derives; §12.9.3: the code point
after a |NumericLiteral| is not an |IdentifierStart| or a |DecimalDigit|. -/
def Scans (src : List Nat) (els : List Element) : Prop :=
  (els.zipIdx.all fun (e, k) => e.i == (if k == 0 then 0 else (els[k - 1]?.map (·.j)).getD 0)) = true ∧
  (els.getLast?.map (·.j)).getD 0 = src.length ∧
  ∀ e ∈ els, e.i < e.j ∧ Derives gl rd cx .lexical (codeAlphabet P) src e.goal [] e.i e.j e.tree ∧
    (∀ h, e.j < h → h ≤ src.length → ¬ ∃ t, Derives gl rd cx .lexical (codeAlphabet P) src e.goal [] e.i h t) ∧
    (e.tree.has .NumericLiteral e.i e.j = true → e.j < src.length →
      ∀ n ∈ [NT.IdentifierStart, NT.DecimalDigit],
        ¬ ∃ t, Derives gl rd cx .lexical (codeAlphabet P) src n [] e.j (e.j + 1) t)

/-- Why §12.10 inserted a virtual semicolon: rule 1 (an offending token after
a line terminator, or `}`), rule 1's `)` of a do-while, rule 2, rule 3. -/
inductive Why where
  | offending
  | paren
  | eof
  | restricted
  deriving Repr, BEq, Inhabited

/-- A token of the syntactic grammar: its code points, whether a line
terminator precedes it, and, for a virtual semicolon, why it was inserted. -/
structure Token where
  text : List Nat
  lt : Bool
  virt : Option Why

/-- The tokens of scanned input elements. -/
def tokensOf (src : List Nat) (els : List Element) : List Token :=
  (els.zipIdx.filter (·.1.isToken)).map fun (e, k) =>
    let before := (els.take k).reverse.takeWhile (!·.isToken)
    ⟨slice src e.i e.j, before.any (·.breaks src), none⟩

/-- The first position from `j` that holds no virtual semicolon. -/
def pastVirt (toks : List Token) (j : Nat) : Nat := j + ((toks.drop j).takeWhile (·.virt.isSome)).length

/-- The syntactic grammar's alphabet: a terminal is a token of its text; a
virtual semicolon only where §12.10 lets one stand (`Gen.semis`'s class of
that `;`); a lexical nonterminal is a real token whose text it derives, the
token's Parse Node being that derivation; a lookahead reads the source's tokens,
past the virtual semicolons (§5.1.6's "input token sequence"). -/
def tokenAlphabet : Alphabet Token where
  term s k x w := match x, w with
    | .text str _, [tok] => tok.text = str.toList.map Char.toNat ∧
        match tok.virt with
        | none => True
        | some why => ∃ c, gl.ctorOf s = some c ∧ ∃ cls, (c, k, cls) ∈ gl.semis ∧
            match cls with
            | .insertable | .forHeaderIfDeclaration => why != .paren
            | .doWhile => True
            | .emptyStatement | .forHeader => False
    | _, _ => False
  phrase _ _ := False
  cond _ _ _ := False
  leaf n tok t := tok.virt = none ∧ Derives gl rd cx .lexical (codeAlphabet P) tok.text n [] 0 tok.text.length t
  noLT toks i := ∀ tok, toks[i]? = some tok → tok.lt = false
  look := pastVirt

/-- A token sequence the goal derives. -/
def Sentence (goal : NT) (ps : List Param) (toks : List Token) (t : Tree) : Prop :=
  Derives gl rd cx .syntactic (tokenAlphabet gl rd cx P) toks goal ps 0 toks.length t

/-- Some sentence of the goal starts with these tokens. -/
def Viable (goal : NT) (ps : List Param) (pre : List Token) : Prop :=
  ∃ rest t, Sentence gl rd cx P goal ps (pre ++ rest) t

/-- §12.10, rule 3's "allowed by some production": viable when line
terminators are ignored. -/
def ViableAnyLT (goal : NT) (ps : List Param) (pre : List Token) : Prop :=
  Viable gl rd cx P goal ps (pre.map fun tok => { tok with lt := false })

/-- §12.10: each virtual semicolon of `toks` is inserted as a rule says, before
an offending token (not allowed by any production) after a line terminator or
when it is `}`, or after `)` where it ends a do-while; at the end of input when
the tokens are no sentence; or before a restricted token after a line
terminator. -/
def ASIOk (goal : NT) (ps : List Param) (toks : List Token) : Prop :=
  ∀ k tok, toks[k]? = some tok → ∀ why, tok.virt = some why →
    let pre := toks.take k
    let next := toks[k + 1]?
    match why with
    | .offending => ∃ nx, next = some nx ∧ nx.virt = none ∧ ¬ Viable gl rd cx P goal ps (pre ++ [nx]) ∧
        (nx.lt ∨ nx.text = "}".toList.map Char.toNat)
    | .paren => ∃ nx, next = some nx ∧ ¬ Viable gl rd cx P goal ps (pre ++ [nx]) ∧
        (pre.getLast?.map (·.text)) = some (")".toList.map Char.toNat)
    | .eof => next = none ∧ ¬ ∃ t, Sentence gl rd cx P goal ps pre t
    | .restricted => ∃ nx, next = some nx ∧ nx.lt ∧ ViableAnyLT gl rd cx P goal ps (pre ++ [nx]) ∧
        ¬ Viable gl rd cx P goal ps (pre ++ [nx])

/-- §12.10's overriding condition at the `;` that ends the |LexicalDeclaration|
of `for ( LexicalDeclaration …`: it is the header's first, never virtual. -/
def ForHeadersExplicit (toks : List Token) : Tree → Prop
  | .leaf .. | .lex .. => True
  | .node n _ _ _ _ kids =>
    (n == .ForStatement → ∀ d ∈ kids, d.nt? = some .LexicalDeclaration →
      ∀ tok, toks[d.span.2 - 1]? = some tok → tok.virt = none) ∧ all kids
where
  all : List Tree → Prop
    | [] => True
    | d :: ds => ForHeadersExplicit toks d ∧ all ds

/-- B.3.3, B.3.5 ("only applies when parsing non-strict code"): no node of such
a production lies in strict mode code. `strict ancestors node` is §11.2.2's
"is strict mode code" (`StrictCode`, with strictness from outside the parse). -/
def NonStrictOk (L : GL) (strict : List Tree → Tree → Prop) : List Tree → Tree → Prop
  | _, .leaf .. | _, .lex .. => True
  | up, t@(.node _ id _ _ _ kids) => (id ∈ L.sloppyIds → ¬ strict up t) ∧ all (t :: up) kids
where
  all (up : List Tree) : List Tree → Prop
    | [] => True
    | d :: ds => NonStrictOk L strict up d ∧ all up ds

/-- The lexical goal §12 prescribes after the tokens `pre`, given whether this is
the start of a |Script| or |Module| and which of |RegularExpressionLiteral|,
|TemplateMiddle| or |TemplateTail| a sentence of the goal permits next ("is permitted"). -/
def lexicalGoal (first : Bool) (regExp template : Bool) : NT :=
  if first then .InputElementHashbangOrRegExp
  else match regExp, template with
    | true, true => .InputElementRegExpOrTemplateTail
    | true, false => .InputElementRegExp
    | false, true => .InputElementTemplateTail
    | false, false => .InputElementDiv

/-- A nonterminal's instance may come next after `pre`. -/
def Permitted (goal : NT) (ps : List Param) (pre : List Token) (x : NT) : Prop :=
  ∃ tok rest t lt, tok.virt = none ∧ (tokenAlphabet gl rd cx P).leaf x tok lt ∧
    Sentence gl rd cx P goal ps (pre ++ tok :: rest) t

/-- The shortest prefix of `toks` with `n` real tokens. -/
def realPrefix : Nat → List Token → List Token
  | 0, _ | _, [] => []
  | n + 1, tok :: toks => tok :: realPrefix (if tok.virt.isNone then n else n + 1) toks

/-- The parse `t` before position `p`: a node started before `p` whole when it ends by `p`, else with
its nonterminal, production, parameters and start, an end after `p` and its children started before
`p` cut; a node starting from `p`, a mark. -/
def Tree.cut (p : Nat) : Tree → Tree
  | t@(.node n id ps i j kids) =>
    if p ≤ i then .leaf p p
    else if j ≤ p then t
    else .node n id ps i (p + 1) (kids.attach.filterMap fun ⟨d, _⟩ => if d.span.1 < p then some (d.cut p) else none)
  | t => if p ≤ t.span.1 then .leaf p p else t

/-- A real token of text `str`. -/
def realTok (str : String) (lt : Bool) : Token := ⟨str.toList.map Char.toNat, lt, none⟩

/-- The classes of leading token §12's goals tell apart. -/
inductive Lead where
  /-- a division or division-assignment -/
  | div
  /-- a |RegularExpressionLiteral| -/
  | re
  /-- a `}` -/
  | rbrace
  /-- a |TemplateMiddle| or |TemplateTail| -/
  | tm
  deriving Repr, BEq, DecidableEq

/-- A real token of the class. -/
def Lead.Holds (c : Lead) (tok : Token) : Prop :=
  tok.virt = none ∧ match c with
    | .div => tok.text = "/".toList.map Char.toNat ∨ tok.text = "/=".toList.map Char.toNat
    | .re => ∃ d, (tokenAlphabet gl rd cx P).leaf .RegularExpressionLiteral tok d
    | .rbrace => tok.text = "}".toList.map Char.toNat
    | .tm => ∃ d, (tokenAlphabet gl rd cx P).leaf .TemplateMiddle tok d ∨
        (tokenAlphabet gl rd cx P).leaf .TemplateTail tok d

/-- Definition reading of spec.html:16887's "syntactic grammar context that is consuming the input
elements": the parse's own position. The classes a token at position `p` of `toks` has in a parse
that is the parse `t` of `toks` before `p` (`Tree.cut`): the items of `t` open at `p` and their
ancestors' items fix the context, never another parse of the same prefix. -/
def Tree.nextBits (goal : NT) (ps : List Param) (toks : List Token) (t : Tree) (p : Nat) (c : Lead) : Prop :=
  ∃ tok rest t', Lead.Holds gl rd cx P c tok ∧ Sentence gl rd cx P goal ps (toks.take p ++ tok :: rest) t' ∧
    t'.cut p = t.cut p

/-- The leading classes permitted after the first `n` real tokens of the parse `t` of `toks`: at the
parse's position (`Tree.nextBits`), and after a semicolon §12.10 inserted there, those before it. -/
def PermitsAt (goal : NT) (ps : List Param) (toks : List Token) (t : Tree) (n : Nat) (c : Lead) : Prop :=
  let pre := realPrefix n toks
  if (toks[pre.length]?.bind (·.virt)).isSome then
    match c with
    | .re => Permitted gl rd cx P goal ps pre .RegularExpressionLiteral
    | .tm => Permitted gl rd cx P goal ps pre .TemplateMiddle ∨ Permitted gl rd cx P goal ps pre .TemplateTail
    | .div => ∃ str ∈ ["/", "/="], ∃ lt, Viable gl rd cx P goal ps (pre ++ [realTok str lt])
    | .rbrace => ∃ lt, Viable gl rd cx P goal ps (pre ++ [realTok "}" lt])
  else t.nextBits gl rd cx P goal ps toks pre.length c

/-- §12: each input element of the parse `t` is read with the goal its context permits (`PermitsAt`),
trivia with the next token's. -/
def GoalsAt (goal : NT) (ps : List Param) (src : List Nat) (els : List Element) (toks : List Token) (t : Tree) :
    Prop :=
  ∀ k e, els[k]? = some e →
    let n := (tokensOf src (els.take k)).length
    ∃ r tm : Bool, (r = true ↔ PermitsAt gl rd cx P goal ps toks t n .re) ∧
      (tm = true ↔ PermitsAt gl rd cx P goal ps toks t n .tm) ∧
      e.goal = lexicalGoal (k == 0 && (goal == .Script || goal == .Module)) r tm

/-! ## B.1.2: ordered alternatives and the group-number condition -/

/-- B.1.2's "each alternative is considered only if previous production alternatives do not match",
as commitment: a node of a nonterminal B.1.2 restates (`GL.orderedNts`) at `i` uses an alternative only
if no earlier alternative of it derives (in `D`) any span from `i`. -/
def Tree.Commits (g : GrammarId) (D : NT → List Param → Nat → Nat → Tree → Prop) : Tree → Prop
  | .leaf .. => True
  | .lex _ t => t.Commits g D
  | .node n id ps i _ kids =>
    (n ∈ gl.orderedNts cx g → ∀ h id' kids' k k', D n ps i h (.node n id' ps i h kids') →
      gl.altPos rd cx g n id = some k → gl.altPos rd cx g n id' = some k' → k ≤ k') ∧ all kids
where
  all : List Tree → Prop
    | [] => True
    | d :: ds => d.Commits g D ∧ all ds

/-- A parse of the whole input with B.1.2's ordered alternatives: a derivation whose every node
commits (`Tree.Commits`), an earlier alternative's match read in `Derives`. -/
def Committed (g : GrammarId) (goal : NT) (ps : List Param) (src : List Nat) (t : Tree) : Prop :=
  Derives gl rd cx g (codeAlphabet P) src goal ps 0 src.length t ∧
    t.Commits gl rd cx g (Derives gl rd cx g (codeAlphabet P) src)

/-- The primitives with `c` as B.1.2's group-number condition. -/
def CodePrims.withGroup (P : CodePrims) (c : List Nat → Tree → Prop) : CodePrims :=
  { P with cond := fun p => match p with
    | .groupNumberAtMostCount => c
    | p => P.cond p }

/-- The nodes of a tree whose production is one of `ids`, the tree's own included. -/
def Tree.countProds (ids : List Nat) : Tree → Nat
  | .leaf .. => 0
  | .lex _ t => t.countProds ids
  | .node _ id _ _ _ kids => (if ids.contains id then 1 else 0) + (kids.attach.map fun ⟨k, _⟩ => k.countProds ids).sum

/-- §22.2.1.5 CapturingGroupNumber: the MV of a |DecimalEscape|'s code points, decimal digits. -/
def decimalMV (cs : List Nat) : Nat := cs.foldl (fun a c => 10 * a + (c - 0x30)) 0

/-- B.1.2's condition of `AtomEscape :: DecimalEscape`, stratified: the CapturingGroupNumber of the
|DecimalEscape| `t` is at most CountLeftCapturingParensWithin (§22.2.1.2, B.1.2.2) of a committed
parse of the input as Pattern[~UnicodeMode, ~UnicodeSetsMode, ~NamedCaptureGroups] with the condition
true ("the |Pattern| containing |DecimalEscape|" being the tree the condition selects). -/
def groupCond (inp : List Nat) (t : Tree) : Prop :=
  ∃ T, Committed gl rd cx (P.withGroup fun _ _ => True) .regExp .Pattern [] inp T ∧
    decimalMV (slice inp t.span.1 t.span.2) ≤ T.countProds gl.capturingIds

/-- A code point grammar's goal (RegExp's |Pattern|, the numeric string
grammar's) parses the text as `t`; with B.1.2's ordered alternatives, a
committed parse, its group-number condition `groupCond`. -/
def ParsesCode (g : GrammarId) (goal : NT) (ps : List Param) (src : List Nat) (t : Tree) : Prop :=
  if gl.ordered cx g then Committed gl rd cx (P.withGroup (groupCond gl rd cx P)) g goal ps src t
  else Derives gl rd cx g (codeAlphabet P) src goal ps 0 src.length t

end Ecma.Grammar
