module

public import Ecma.Grammar.Core

@[expose] public section

/-!
# The grammar notation, executable

What reading GL needs beyond its data: the context a parse is under, the Annex B overlays and
readings in effect (`GL.alts`), production ids of right-hand sides, parameters through a
reference (`applyArgs`) and guards, and chain and unit productions. Definitions only; the derivation relation
(`Ecma.Grammar.Derives`) and the parser (`Parse`) both read them.
-/

namespace Ecma.Grammar

/-- What a parse is under (§5.1.2, sec-parsing; Annex B, sec-additional-ecmascript-features-for-web-browsers):
the goal is a Module, and the Annex B overlay sections the host supports (normative optional). Strictness is
regional (`NonStrictOk`). -/
structure Ctx where
  module : Bool
  annexB : AnnexB.Set
  deriving Repr, BEq, Inhabited

/-- GL as the derivation relation reads it (§5.1, sec-syntactic-and-lexical-grammars; §5.1.6,
sec-grammar-notation; §12.10, sec-automatic-semicolon-insertion): each grammar's rules in spec order, the
production ids of their right-hand sides, the definition blocks (the overlays'
sections, modes and conditions), and §12.10's class of each `;` of the syntactic
grammar (written production, position). -/
structure GL where
  grammars : List (GrammarId × List Rule)
  /-- The production id of each right-hand side of `grammars`, in `prodsOf`'s order, as runs
  (`idsOfRuns`): its alphabetical index among all expanded right-hand sides. -/
  ids : List (Nat × Nat)
  /-- The count of production ids. -/
  next : Nat
  blocks : List Block
  semis : List (Nat × Nat × Semi)

/-- GL's right-hand sides by production id (`prodsById`): entry `n` is the right-hand side `ids`
numbers `n`. -/
def GL.byId (gl : GL) : Array (Option Prod) := prodsById gl.grammars gl.ids gl.next

/-- The grammar an Annex B section overlays. -/
def overlayGrammar : AnnexB → GrammarId
  | .htmlLikeComments => .lexical
  | .regExpPatterns => .regExp
  | .functionDeclarationsInIfStatement | .initializersInForIn => .syntactic

/-- An overlay's condition, as far as the context decides it: `nonStrict`
holds here, and `NonStrictOk` excludes the overlay's nodes in strict mode code. -/
def condHolds (cx : Ctx) : OverlayCond → Bool
  | .always | .nonStrict => true
  | .notModule => !cx.module

/-- The grammar whose definitions a grammar uses for the nonterminals it does
not define: the RegExp and numeric string grammars use the lexical grammar's. -/
def baseGrammar : GrammarId → Option GrammarId
  | .regExp | .numericString => some .lexical
  | _ => none

/-- The code point grammars, in the order a goal is tried. Annex B's rules enter them through `GL.overlays`. -/
def codeGrammars : List GrammarId := [.numericString, .lexical, .regExp, .json]

/-- A rule's written productions as alternatives: a `one of` terminal is the
alternative of that terminal alone. -/
def writtenAlts (r : Rule) : List Alt :=
  match r.body with
  | .alts as => as
  | .oneOf rows => rows.flatten.map fun t => ⟨[], [.sym (.t t) false], none⟩

/-- An alternative in effect (§5.1.6, sec-grammar-notation): the grammar and rule it is written in and its
index among the rule's written productions. -/
structure Src where
  grammar : GrammarId
  rule : Rule
  idx : Nat
  alt : Alt
  deriving Repr, BEq, DecidableEq, Inhabited

/-- All written alternatives of rule `r` in grammar `g` as `Src` entries (§5.1.6, sec-grammar-notation). -/
def srcsOf (g : GrammarId) (r : Rule) : List Src :=
  (writtenAlts r).zipIdx.map fun (a, i) => ⟨g, r, i, a⟩

/-- The rules of grammar `g` in `gl` (§5.1, sec-syntactic-and-lexical-grammars). -/
def GL.rulesOf (gl : GL) (g : GrammarId) : List Rule := (gl.grammars.lookup g).getD []

/-- The pinned definition of `n` in grammar `g`, or in its base grammar. -/
def GL.pinned (gl : GL) (g : GrammarId) (n : NT) : List Src :=
  match (gl.rulesOf g).find? (·.lhs == n) with
  | some r => srcsOf g r
  | none => match baseGrammar g with
    | some b => ((gl.rulesOf b).find? (·.lhs == n)).map (srcsOf b) |>.getD []
    | none => []

/-- The overlays in effect on grammar `g`, in spec order, with their modes. -/
def GL.overlays (gl : GL) (cx : Ctx) (g : GrammarId) : List (Block × OverlayMode) :=
  if !cx.annexB.any then [] else gl.blocks.filterMap fun b => match b.kind with
    | .overlay s m c => if overlayGrammar s == g && cx.annexB.has s && condHolds cx c then some (b, m) else none
    | _ => none

/-- The alternatives of `n` in effect in grammar `g` with the overlays in effect:
`extend` adds the alternatives it does not restate, `replace` replaces the
definition. -/
def GL.alts (gl : GL) (cx : Ctx) (g : GrammarId) (n : NT) : List Src :=
  (gl.overlays cx g).foldl (fun acc (b, m) =>
    match b.rules.find? (·.lhs == n), m with
    | none, _ => acc
    | some r, .extend => acc ++ (srcsOf .annexB r).filter fun s => !acc.any (·.alt == s.alt)
    | some r, .replace => srcsOf .annexB r) (gl.pinned g n)

/-- The production id of a right-hand side: the number GL gives it (`GL.byId`). -/
def GL.prodId (gl : GL) (s : Src) (m : List Bool) : Option Nat :=
  let hit := fun (p : Prod) => p.grammar == s.grammar && p.rule.lhs == s.rule.lhs && p.alt == s.idx && p.mask == m
  gl.byId.findIdx? (·.any hit)

/-- The written production index (`Production` constructor) of a right-hand side. -/
def GL.ctorOf (gl : GL) (s : Src) : Option Nat :=
  ((prodsOf gl.grammars).find? fun p => p.grammar == s.grammar && p.rule.lhs == s.rule.lhs && p.alt == s.idx).map (·.ctor)

/-- B.1.2 ("each alternative is considered only if previous production alternatives do not
match"): grammar `g`'s alternatives are ordered, §B.1.2's overlay being in effect on it. -/
def GL.ordered (gl : GL) (cx : Ctx) (g : GrammarId) : Bool :=
  (gl.overlays cx g).any fun (b, _) => b.kind matches .overlay .regExpPatterns _ _

/-- The nonterminals B.1.2's ordering sentence orders on grammar `g`: those its overlay restates. -/
def GL.orderedNts (gl : GL) (cx : Ctx) (g : GrammarId) : List NT :=
  (gl.overlays cx g).flatMap fun (b, _) => if b.kind matches .overlay .regExpPatterns _ _ then b.rules.map (·.lhs) else []

/-- The position in `GL.alts` of the alternative of `n` with production id `id`. -/
def GL.altPos (gl : GL) (cx : Ctx) (g : GrammarId) (n : NT) (id : Nat) : Option Nat :=
  ((gl.alts cx g n).zipIdx.find? fun (s, _) => (masks s.alt.opts).any (gl.prodId s · == some id)).map (·.2)

/-- The right-hand side `( GroupSpecifier? Disjunction )`. -/
def capturingRhs : List Item → Bool
  | [.sym (.t (.text "(" _)) false, .sym (.nt .GroupSpecifier _) true, .sym (.nt .Disjunction _) false,
     .sym (.t (.text ")" _)) false] => true
  | _ => false

/-- §22.2.1.2, B.1.2.2: the productions of a left-capturing parenthesis,
`Atom :: ( GroupSpecifier? Disjunction )` and B.1.2's same right-hand side of |ExtendedAtom|. -/
def GL.capturingIds (gl : GL) : List Nat :=
  gl.byId.toList.zipIdx.filterMap fun (o, id) => o.bind fun p =>
    if (p.rule.lhs == .Atom || p.rule.lhs == .ExtendedAtom) && (p.altOf.map (capturingRhs ·.rhs)).getD false
    then some id else none

/-- §5.1.6: a reference's arguments give the parameters set for its nonterminal. -/
def applyArgs (ps : List Param) (args : List Arg) : List Param :=
  args.filterMap fun a => match a.sign with
    | .plus => some a.param
    | .tilde => none
    | .quest => if ps.contains a.param then some a.param else none

/-- A guard condition holds under the parameters set. -/
def Guard.holds (ps : List Param) (g : Guard) : Bool := ps.contains g.param == g.plus

/-- The ids of the productions of overlays that apply only to non-strict code. -/
def GL.sloppyIds (L : GL) : List Nat :=
  L.byId.toList.zipIdx.filterMap fun (o, id) => o.bind fun p =>
    if p.grammar == .annexB && L.blocks.any (fun b => b.kind matches .overlay _ _ .nonStrict && b.rules.contains p.rule)
    then some id else none

/-- §5.1.1: the sole nonterminal of a chain production's right-hand side (one
nonterminal symbol and zero or more terminals), with its optional symbols'
presences `m`; none for any other right-hand side. -/
def chainNt (a : Alt) (m : List Bool) : Option NT :=
  let rec go : List Item → List Bool → List NT
    | [], _ => []
    | .sym (.nt n _) true :: is, b :: bs => (if b then [n] else []) ++ go is bs
    | .sym (.t _) true :: is, _ :: bs => go is bs
    | .sym (.nt n _) false :: is, bs => n :: go is bs
    | .butNot (.nt n _) _ :: is, bs => n :: go is bs
    | _ :: is, bs => go is bs
  match go a.rhs m with
  | [n] => some n
  | _ => none

/-- The sole nonterminal of a unit right-hand side (one nonterminal symbol and no terminals),
with its optional symbols' presences `m`; none for any other right-hand side. -/
def unitNt (a : Alt) (m : List Bool) : Option NT :=
  let rec go : List Item → List Bool → List (Option NT)
    | [], _ => []
    | .sym (.nt n _) true :: is, b :: bs => (if b then [some n] else []) ++ go is bs
    | .sym (.t _) true :: is, b :: bs => (if b then [none] else []) ++ go is bs
    | .sym (.nt n _) false :: is, bs => some n :: go is bs
    | .sym (.t _) false :: is, bs => none :: go is bs
    | .butNot (.nt n _) _ :: is, bs => some n :: go is bs
    | .butNot (.t _) _ :: is, bs => none :: go is bs
    | _ :: is, bs => go is bs
  match go a.rhs m with
  | [some n] => some n
  | _ => none

/-- A terminal's text; a named code point is that code point (`<USP>`, a class, is ""). -/
def Terminal.str : Terminal → String
  | .text s _ => s
  | .cp n => (n.codePoint.map fun c => String.singleton (Char.ofNat c)).getD ""

/-- The terminals among a right-hand side's present symbols (with its optional symbols' presences
`m`), each by its position among them. -/
def presentTerms (a : Alt) (m : List Bool) : List (Nat × String) :=
  let rec go : List Item → List Bool → List (Option String)
    | [], _ => []
    | .sym (.nt _ _) true :: is, b :: bs => (if b then [none] else []) ++ go is bs
    | .sym (.t x) true :: is, b :: bs => (if b then [some x.str] else []) ++ go is bs
    | .sym (.nt _ _) false :: is, bs => none :: go is bs
    | .sym (.t x) false :: is, bs => some x.str :: go is bs
    | .butNot (.nt _ _) _ :: is, bs => none :: go is bs
    | .butNot (.t x) _ :: is, bs => some x.str :: go is bs
    | _ :: is, bs => go is bs
  (go a.rhs m).zipIdx.filterMap fun (t, i) => t.map (i, ·)

/-- `GL.chain`, `GL.unit` and `GL.terms` of every production, by production id, and `GL.paramsOf`'s
productions, built once: each a lookup, where the `GL` functions rebuild `prodsOf` per call. -/
structure GL.Tab where
  prods : Array Prod
  chain : Array (Option NT)
  unit : Array (Option NT)
  terms : Array (List (Nat × String))

/-- The tables of `L`. -/
def GL.tab (L : GL) : GL.Tab :=
  let ps := L.byId
  { prods := (prodsOf L.grammars).toArray
    chain := ps.map fun o => o.bind fun p => p.altOf.bind (chainNt · p.mask)
    unit := ps.map fun o => o.bind fun p => p.altOf.bind (unitNt · p.mask)
    terms := ps.map fun o => (o.bind fun p => p.altOf.map (presentTerms · p.mask)).getD [] }

/-- `GL.chain` by the tables. -/
def GL.Tab.chainOf (T : GL.Tab) (id : Nat) : Option NT := (T.chain[id]?).join

/-- `GL.unit` by the tables. -/
def GL.Tab.unitOf (T : GL.Tab) (id : Nat) : Option NT := (T.unit[id]?).join

/-- `GL.terms` by the tables. -/
def GL.Tab.termsOf (T : GL.Tab) (id : Nat) : List (Nat × String) := (T.terms[id]?).getD []

/-- `GL.paramsOf` by the tables. -/
def GL.Tab.paramsOf (T : GL.Tab) (k : Nat) : List Nat :=
  ((T.prods.find? (·.rule.lhs.ctorIdx == k)).map fun p => p.rule.params.map (·.ctorIdx)).getD []

end Ecma.Grammar
