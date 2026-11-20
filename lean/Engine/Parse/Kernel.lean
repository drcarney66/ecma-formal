module

public import Engine.Parse.Core
public import Std.Data.HashSet

@[expose] public section

/-!
# The kernel: checked Parse Nodes

A search runs over positions of an alphabet (`Alpha`): code points for the lexical, numeric
string and RegExp grammars, token boundaries for the syntactic grammar. `mk` makes the Parse Node
of one right-hand side from its pieces only after checking them against GL's production, as
`Ecma.Grammar.Derives` reads it: the alternative in effect in the parse context, the guard, the presence mask, each terminal,
phrase and lexical leaf through the alphabet, each child's nonterminal, parameters (`applyArgs`)
and span, contiguity, lookahead, `[no LineTerminator here]`, `but not` and the
`[> but only if …]` conditions. A failed check is a stop, never a node and never "no parse".
The negative items read the alphabet's own decision of a nonterminal (`negSpan`, `negAny`).
-/

namespace Engine.Parse

open Ecma.Grammar

/-- Positions as half-open intervals `[iv[2k], iv[2k+1])`: ascending, nonempty, none adjacent. -/
structure Ends where
  iv : Array Nat := #[]
  deriving BEq, Inhabited

/-- A memo entry: the end positions found, whether they are all of them, the furthest position its
evaluation read the alphabet at, the furthest a match in it reached, and the alphabet's generation. -/
structure Entry where
  ends : Ends
  final : Bool
  hzn : Nat := 0
  far : Nat := 0
  gen : Nat := 0

/-- Grammar, nonterminal, parameters, position, and whether B.1.2's nodes commit. -/
abbrev Key := Nat × Nat × Nat × Nat × Bool

/-- A search's state: the memo, the entries in progress and the ones read meanwhile, the steps
left, the lexer's tokens by position and goal and lexical leaves by nonterminal and position (as
entries `T`), the furthest position a match reached, the forward passes of the direct left
recursions built, B.1.2's first alternatives deriving some span, whether a lookahead read past a
waiting virtual `;`, the furthest position the alphabet was read at (`far` and `hzn` count from
the start of the entry in progress), the alphabet's generation, by generation the first position
changed since, and what each boundary was asked over all rounds (`Syntax.ask`). -/
structure St (T : Type) where
  memo : Std.HashMap Key Entry := {}
  active : Std.HashSet Key := {}
  reads : Std.HashSet Key := {}
  steps : Nat
  toks : Std.HashMap (Nat × Nat) T := {}
  leaves : Std.HashMap (Nat × Nat) T := {}
  far : Nat := 0
  fwd : Std.HashMap (Key × Nat × Nat × Bool) (Array Ends × Array (Std.HashMap Nat (Array Nat))) := {}
  first : Std.HashMap Key (Option Eff) := {}
  spans : Bool := false
  hzn : Nat := 0
  gen : Nat := 0
  cuts : Array Nat := #[]
  asks : Std.HashMap Nat Nat := {}

abbrev SM (T : Type) := StateT (St T) (Except Stop)

/-- The next generation, the alphabet changed from position `b` on. -/
def St.cut {T : Type} (s : St T) (b : Nat) : St T := Id.run do
  let mut cuts := s.cuts.push b
  for i in [0:s.gen] do
    if cuts[s.gen - 1 - i]! ≤ b then break
    cuts := cuts.set! (s.gen - 1 - i) b
  return { s with cuts, gen := s.gen + 1 }

/-- Entry `e` at `i` holds in `s`'s generation: made in it, or final, with `i` and all it read or reached before every change since. -/
def St.valid {T : Type} (s : St T) (i : Nat) (e : Entry) : Bool :=
  e.gen == s.gen ||
    (e.final && e.hzn < s.cuts.getD e.gen 0 && e.far < s.cuts.getD e.gen 0 && i < s.cuts.getD e.gen 0)

/-- What a search reads besides GL: its grammar, and its alphabet over positions. -/
structure Alpha (N T : Type) where
  g : GrammarId
  /-- the erratum readings in effect -/
  rd : List RuleReading
  /-- the parse context: the |Module| goal, Annex B -/
  cx : Ctx
  /-- terminal `x` at item `k` of written alternative `alt` of `lhs`'s rule, from `p`: its end -/
  term : NT → Nat → Nat → Terminal → Nat → SM T (Option Nat)
  /-- one input element from `p` derived as a nonterminal this grammar does not define -/
  leaf : NT → Nat → SM T (Option Nat)
  /-- a descriptive phrase from `p` -/
  phrase : Phrase → Nat → SM T (Option Nat)
  /-- a `[> but only if …]` condition on the node over `a` to `b` -/
  cond : Phrase → Nat → Nat → SM T Bool
  /-- no line terminator before the element at `p` -/
  noLT : Nat → SM T Bool
  /-- the input from `p` starts with the lookahead sequence -/
  starts : List LookItem → Nat → SM T Bool
  /-- whether the child `n` of `lhs` may end at `e` -/
  keep : NT → NT → Nat → Bool
  /-- `keep lhs n` holds at every end -/
  keepAll : NT → NT → Bool := fun _ _ => false
  /-- a match reached `e` -/
  hit : Nat → SM T Unit
  /-- the code point span and the code points of positions `lo` to `hi` -/
  span : Nat → Nat → SM T (Nat × Nat)
  text : Nat → Nat → SM T (Subarray Nat)
  /-- the lexical Parse Node of the leaf `n` over `a` to `b` -/
  leafNode : NT → Nat → Nat → SM T N
  /-- a negative item's nonterminal derives exactly `a` to `b` -/
  negSpan : NT → List Param → Nat → Nat → SM T Bool
  /-- a lookahead's nonterminal derives some input from `a` -/
  negAny : NT → Nat → SM T Bool

variable {N T : Type}

def liftE {α : Type} (e : Except Stop α) : SM T α := match e with
  | .ok a => pure a
  | .error s => throw s

/-- A lookahead restriction holds at `j`. -/
def lookOk (A : Alpha N T) : Lookahead → Nat → SM T Bool
  | .eq q, j => A.starts q j
  | .ne q, j => return !(← A.starts q j)
  | .mem qs, j => qs.anyM (A.starts · j)
  | .notMem qs, j => return !(← qs.anyM (A.starts · j))
  | .notMemNT n, j => return !(← A.negAny n j)

/-- Symbol `y` derives `i` to `h`. -/
def symDerives (A : Alpha N T) (lhs : NT) (alt k : Nat)
    (ps : List Param) (i h : Nat) : Sym → SM T Bool
  | .t x => return (← A.term lhs alt k x i) == some h
  | .nt n args =>
    if (ruleIn A.g n.ctorIdx).isSome then A.negSpan n (applyArgs ps args) i h
    else return (← A.leaf n i) == some h

/-- The input `i` to `h` is one of the excluded symbols. -/
def excluded (A : Alpha N T) (lhs : NT) (alt k : Nat)
    (ps : List Param) (i h : Nat) : Exclusion → SM T Bool
  | .sym y => symDerives A lhs alt k ps i h y
  | .oneOf ys _ => ys.anyM (symDerives A lhs alt k ps i h)

/-- A child piece of a right-hand side: a terminal's or phrase's span, a nonterminal's or a
leaf's node with its span, an absent optional symbol, or a zero-width item. -/
inductive Piece (N : Type) where
  | span (i j : Nat)
  | kid (n : N) (i j : Nat)
  | absent
  | zero

/-- The condition the item after a nonterminal places on it, if any. -/
def condAfter : List Item → Option Phrase
  | .onlyIf c :: _ => some c
  | _ => none

/-- Checks items from index `k` against pieces from `pos`, with the presences `mask`; the end
and the child entries. -/
def walk (B : Builder N) (A : Alpha N T) (lhs : NT) (alt : Nat)
    (ps : List Param) :
    Nat → List Item → List Bool → List (Piece N) → Nat → Array (Nat × Option N) → SM T (Nat × Array (Nat × Option N))
  | _, [], [], [], pos, kids => pure (pos, kids)
  | k, .sym x true :: is, false :: ms, .absent :: pcs, pos, kids =>
    walk B A lhs alt ps (k + 1) is ms pcs pos (match x with | .nt n _ => kids.push (n.ctorIdx, none) | .t _ => kids)
  | k, .sym x true :: is, true :: ms, pc :: pcs, pos, kids => do
    let (pos', kids') ← one k x is pc pos kids
    walk B A lhs alt ps (k + 1) is ms pcs pos' kids'
  | k, .sym x false :: is, ms, pc :: pcs, pos, kids => do
    let (pos', kids') ← one k x is pc pos kids
    walk B A lhs alt ps (k + 1) is ms pcs pos' kids'
  | k, .butNot base ex :: is, ms, pc :: pcs, pos, kids => do
    let (pos', kids') ← one k base [] pc pos kids
    if ← excluded A lhs alt k ps pos pos' ex then throw (.check "an excluded symbol")
    walk B A lhs alt ps (k + 1) is ms pcs pos' kids'
  | k, .phrase p :: is, ms, .span a b :: pcs, pos, kids => do
    unless a == pos && (← A.phrase p a) == some b do throw (.check "a phrase")
    walk B A lhs alt ps (k + 1) is ms pcs b kids
  | k, .lookahead l :: is, ms, .zero :: pcs, pos, kids => do
    unless ← lookOk A l pos do throw (.check "a lookahead")
    walk B A lhs alt ps (k + 1) is ms pcs pos kids
  | k, .noLT :: is, ms, .zero :: pcs, pos, kids => do
    unless ← A.noLT pos do throw (.check "a line terminator")
    walk B A lhs alt ps (k + 1) is ms pcs pos kids
  | k, .empty :: is, ms, .zero :: pcs, pos, kids => walk B A lhs alt ps (k + 1) is ms pcs pos kids
  | k, .onlyIf _ :: is, ms, .zero :: pcs, pos, kids => walk B A lhs alt ps (k + 1) is ms pcs pos kids
  | _, _, _, _, _, _ => throw (.check "pieces against the right-hand side")
where
  /-- One present symbol (or `but not`'s base) at `pos`. -/
  one (k : Nat) (x : Sym) (is : List Item) : Piece N → Nat → Array (Nat × Option N) → SM T (Nat × Array (Nat × Option N))
    | .span a b, pos, kids => match x with
      | .t t => do
        unless a == pos && (← A.term lhs alt k t a) == some b do throw (.check "a terminal")
        pure (b, kids)
      | .nt .. => throw (.check "a span for a nonterminal")
    | .kid c a b, pos, kids => match x with
      | .nt n args => do
        unless B.nt c == n.ctorIdx && a == pos && A.keep lhs n b && B.span c == (← A.span a b) do
          throw (.check "a child")
        if (ruleIn A.g n.ctorIdx).isSome then
          unless B.args c == applyArgs ps args do throw (.check "a child's parameters")
        else
          unless B.args c == [] && (← A.leaf n a) == some b do throw (.check "a leaf")
        if let some p := condAfter is then
          unless ← A.cond p a b do throw (.check "a condition")
        pure (b, kids.push (n.ctorIdx, some c))
      | .t _ => throw (.check "a node for a terminal")
    | _, _, _ => throw (.check "a missing piece")

/-- The checked Parse Node of production `p` with parameters `ps` over positions `lo` to `hi`. -/
def mk (B : Builder N) (A : Alpha N T) (stamp p : Nat)
    (ps : List Param) (lo hi : Nat) (pieces : List (Piece N)) : SM T N := do
  let some P := prodOf A.rd p | throw (.check "no such production")
  let some es := effAlts A.g A.rd A.cx P.rule.lhs.ctorIdx | throw (.check "no rule in effect")
  let some ef := es.find? (fun e => e.wg == P.grammar && e.idx == P.alt && e.rule == P.rule &&
      e.fresh == isFresh p) | throw (.check "not an alternative in effect")
  let a := ef.alt
  unless a.guard.all (Guard.holds ps) do throw (.check "a guard")
  let (e, kids) ← walk B A P.rule.lhs P.alt ps 0 a.rhs P.mask pieces lo #[]
  unless e == hi do throw (.check "the span")
  let (i, j) ← A.span lo hi
  pure (B.node stamp i j p P.rule.lhs.ctorIdx ps kids (← A.text lo hi))

end Engine.Parse
