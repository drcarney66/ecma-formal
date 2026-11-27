module

public import Engine.Parse.Lex

@[expose] public section

/-!
# The syntactic grammar

The syntactic grammar over tokens (`Ecma.Grammar.tokenAlphabet`), by the search. A position is a
token boundary `2 * p + v`: `p` the code point after the last token, `v` whether a virtual `;`
inserted at `p` is consumed. A terminal is a token of its text, a lexical nonterminal a token it
derives, each read by `lexAt` under the goal the expected token implies (`lexicalGoalOf`). A
virtual `;` stands only where §12.10's class of that `;` (`virtualOk`) lets it, and the `;` that
ends a `for` header's LexicalDeclaration is never virtual (`ForHeadersExplicit`).

`run` inserts the virtual `;` of §12.10 one at a time (`Ecma.Grammar.ValidASI`): when no parse
spans the input, the token after the furthest boundary reached (`far`) is not allowed by any
production; if a line terminator precedes it, or it is `}`, or the input ends there, or the token
before it is `)` (for a do-while's `;`), a `;` is inserted before it and the search runs again
(preserving the lexer and leaf caches); otherwise there is no parse.
-/

namespace Engine.Parse.Syntax

open Ecma.Grammar Search Lex

/-- The lexical goal a lexical nonterminal is read under (`Ecma.Grammar.lexicalGoalOf`). -/
def goalOf (n : NT) : NT := lexicalGoalOf n

variable {N : Type} (B : Builder N) (cs : Array Nat) (first : Bool) (cx : Ctx) (stamp : Nat) (vs : List (Nat × Bool))

/-- A token whose NumericLiteral §12.9.3's follow rule rejects is none. -/
def tokOf : Lexed → Lexed
  | .follow j => .bad j
  | r => r

/-- The lexical nonterminal `n` as the token `r`, ending at `2 * r`'s end: the code point search
finds a derivation of `n` over the token's code points. -/
def leafOf (n : NT) : Lexed → Except Stop (Option Nat)
  | .tok t => do
    let r ← (Code.parse (T := Unit) B (cs.extract t.i t.j) .lexical cx t.i cs 0 n []).run'
      { steps := Code.budget (t.j - t.i) }
    pure (r.map fun _ => 2 * t.j)
  | _ => pure none

/-- A memo entry: the token `lexAtPure` reads at `p` under `goal`, or the leaf `n` from `s / 2`, each
with its key. -/
inductive Memo where
  | tok (p : Nat) (goal : NT) (r : Lexed) (h : lexAtPure B cs first cx goal p = .ok r)
  | leaf (n : NT) (p : Nat) (r : Option Nat)
      (h : ∃ t, lexAtPure B cs first cx (goalOf n) p = .ok t ∧ leafOf B cs cx n t = .ok r)

/-- The token from code point `p` under `goal`, read once, with its reading. -/
def lexP (goal : NT) (p : Nat) : SM (Memo B cs first cx) {r : Lexed // lexAtPure B cs first cx goal p = .ok r} := do
  let k := (p, goal.ctorIdx)
  if let some (.tok p' g' r h) := (← get).toks[k]? then
    if hk : p' = p ∧ g' = goal then return ⟨r, hk.1 ▸ hk.2 ▸ h⟩
  match h : lexAtPure B cs first cx goal p with
  | .ok r =>
    modify fun s => { s with toks := s.toks.insert k (.tok p goal r h) }
    return ⟨r, h⟩
  | .error e => throw e

/-- The token from code point `p` under `goal`, read once; a NumericLiteral that §12.9.3's follow
rule rejects is no token. -/
def lex (goal : NT) (p : Nat) : SM (Memo B cs first cx) Lexed := do
  return tokOf (← lexP B cs first cx goal p).1

/-- A virtual `;` waits at `s` (`Ecma.Grammar.vsPending`). -/
def pending (s : Nat) : Bool := vsPending vs s

def textIs (t : Tok) (str : String) : Bool := (cs.extract t.i t.j).toList == str.toList.map Char.toNat

/-- Terminal `x` (item `k` of `s`) from boundary `i` (`Ecma.Grammar.SynTerm`). -/
def term (s : Src) (k : Nat) (x : Terminal) (i : Nat) : SM (Memo B cs first cx) (Option Nat) := do
  let .text str _ := x | return none
  if pending vs i then
    return if str == ";" && virtualOk s k (vsParen vs (i / 2)) then some (i + 1) else none
  match ← lex B cs first cx .InputElementDiv (i / 2) with
  | .tok t => return if noCross vs (i / 2) t.j && textIs cs t str then some (2 * t.j) else none
  | _ => return none

/-- The lexical nonterminal `n` as one token from boundary `i` (`Ecma.Grammar.SynLeaf`). -/
def leaf (n : NT) (i : Nat) : SM (Memo B cs first cx) (Option Nat) := do
  if pending vs i then return none
  let p := i / 2
  let k := (n.ctorIdx, p)
  if let some (.leaf n' p' r _) := (← get).leaves[k]? then
    if n' = n ∧ p' = p then
      return r.filter fun b => noCross vs p (b / 2)
  let ⟨t, ht⟩ ← lexP B cs first cx (goalOf n) p
  match hr : leafOf B cs cx n t with
  | .ok r =>
    modify fun st => { st with leaves := st.leaves.insert k (.leaf n p r ⟨t, ht, hr⟩) }
    return r.filter fun b => noCross vs p (b / 2)
  | .error e => throw e

/-- No line terminator before the token at boundary `s` (`Ecma.Grammar.SynNoLT`). -/
def noLT (s : Nat) : SM (Memo B cs first cx) Bool := do
  if pending vs s then return true
  let (k, lt) := skip B cs first cx (s / 2)
  return k ≥ cs.size || !lt

/-- The boundary a lookahead reads from `s`: past a waiting virtual `;` (`Ecma.Grammar.SynLook`). -/
def look (s : Nat) : Nat := SynLook vs s

/-- The source tokens from `s` start with the lookahead sequence (`Ecma.Grammar.SynStarts`). -/
def starts : List LookItem → Nat → SM (Memo B cs first cx) Bool
  | [], _ => pure true
  | .noLT :: rest, s => do
    if ← noLT B cs first cx vs (look vs s) then starts rest s else pure false
  | .t x :: rest, s => do
    let .text str _ := x | return false
    let p := (look vs s) / 2
    match ← lex B cs first cx .InputElementDiv p with
    | .tok t => if noCross vs p t.j && textIs cs t str then starts rest (2 * t.j) else pure false
    | _ => pure false

/-- The code point span of positions `lo` to `hi` (`Grammar.tokenSpan`). -/
def span (lo hi : Nat) : SM (Memo B cs first cx) (Nat × Nat) := do
  let (k, _) := skip B cs first cx (lo / 2)
  if hi / 2 > lo / 2 then return (k, hi / 2)
  return if k < cs.size then (k, k) else (lo / 2, lo / 2)

/-- The tokens' alphabet, with the virtual `;` list `vs`. -/
def alpha : Alpha N (Memo B cs first cx) where
  g := .syntactic
  cx := cx
  term := term B cs first cx vs
  leaf := leaf B cs first cx vs
  phrase _ _ := pure none
  cond _ _ _ := pure false
  noLT := noLT B cs first cx vs
  starts := starts B cs first cx vs
  keep := forKeep
  keepAll lhs n := !(lhs == .ForStatement && n == .LexicalDeclaration)
  hit e := modify fun s => { s with far := max s.far e }
  span := span B cs first cx
  text lo hi := do let (i, j) ← span B cs first cx lo hi; return view cs i j
  leafNode n a b := do
    if pending vs a then throw (.check "a leaf at a virtual semicolon")
    match ← lex B cs first cx (goalOf n) (a / 2) with
    | .tok t =>
      unless 2 * t.j == b && noCross vs (a / 2) t.j do throw (.check "a leaf's span")
      match (Code.parse (T := Unit) B (cs.extract t.i t.j) .lexical cx t.i cs stamp n []).run'
          { steps := Code.budget (t.j - t.i) } with
      | .ok (some node) => pure node
      | .ok none => throw (.check "a leaf with no lexical derivation")
      | .error e => throw e
    | _ => throw (.check "a leaf without its token")
  negSpan _ _ _ _ := pure false
  negAny _ _ := pure false

/-- The recursion depth bound over `n` code points. -/
def depth (n : Nat) : Nat := 64 * n + 2000

/-- The steps a parse of `n` code points may take. -/
def budget (n : Nat) : Nat := 20000 * (n + 1)

/-- Where §12.10 inserts a virtual `;` when no parse reaches past `f` (`Ecma.Grammar.NextASI`). -/
def insertion (f : Nat) : SM (Memo B cs first cx) (Option (Nat × Bool)) := do
  if f % 2 == 1 || !vs.all (fun (q, _) => q != f / 2) then return none
  let p := f / 2
  match ← lex B cs first cx .InputElementDiv p with
  | .eof _ => return some (p, false)
  | .tok t =>
    if t.lt || textIs cs t "}" then return some (p, false)
    if 0 < p && cs[p - 1]? == some 0x29 then return some (p, true)
    return none
  | _ => return none

/-- Goal `goal` with parameters `ps` over the tokens of `cs` in context `cx`: its Parse Node, or none
when no parse exists. -/
def run (goal : NT) (ps : List Param) : Except Stop (Option N) := do
  let size := 2 * cs.size + 2
  let first := firstOf goal
  let rec go : Nat → List (Nat × Bool) → SM (Memo B cs first cx) (Option N)
    | 0, _ => throw .fuel
    | fuel + 1, vs => do
      modify fun s => { s with memo := {}, active := {}, reads := {}, far := 0, fwd := {}, first := {} }
      let A := alpha B cs first cx stamp vs
      let es ← finalEnds A size (depth cs.size) goal ps 0
      let mut done : Option Nat := none
      for e in es.toList do
        if (skip B cs first cx (e / 2)).1 ≥ cs.size && !pending vs e && vs.all (fun (p, _) => p ≤ e / 2) then
          if done.isSome then throw (.ambiguous s!"{goal.name}: two ends")
          done := some e
      if let some e := done then
        let nd ← build A B size (depth cs.size) stamp (depth cs.size) goal ps 0 e
        unless B.nt nd == goal.ctorIdx do throw (.check "a node of another nonterminal")
        return some nd
      match ← insertion B cs first cx vs (← get).far with
      | some (p, paren) => go fuel (vs ++ [(p, paren)])
      | none => return none
  (go (cs.size + 2) []).run' { steps := budget cs.size }

end Engine.Parse.Syntax
