module

public import Engine.Parse.Lex

@[expose] public section

/-!
# The syntactic grammar

The syntactic grammar over tokens (`Ecma.Grammar.tokenAlphabet`), by the search. A position is a
token boundary `2 * p + v`: `p` the code point after the last token, `v` whether a virtual `;`
inserted at `p` is consumed. A terminal is a token of its text, a lexical nonterminal a token it
derives, each read by `lexAt` under the goal the expected token implies (`/`, `/=` and `}` under
InputElementDiv, a RegularExpressionLiteral under InputElementRegExp, a TemplateMiddle or
TemplateTail under InputElementTemplateTail; the other tokens read alike under every goal). A
virtual `;` stands only where §12.10's class of that `;` (`Gen.semis`) lets it, and the `;` that
ends a `for` header's LexicalDeclaration is never virtual (`ForHeadersExplicit`).

`run` inserts the virtual `;` of §12.10 one at a time: when no parse spans the input, the token
after the furthest position a match reached is not allowed by any production; if a line
terminator precedes it, or it is `}`, or the input ends there, or the token before it is `)`
(then only a do-while's `;` may take it), a `;` is inserted before it and the search runs again;
otherwise there is no parse. A lookahead reads past an inserted `;`; with LookaheadSourceTokens read
literally (`lit`), `run` gives no decision once one has. §12 reads the token after an inserted `;`
before the `;` (spec.html:16889), so no decision is given where a parse has a token starting with `/` there
or where a template continuation is read right after one.

No decision either where a round that inserts or finds a parse has a boundary asked for both a
`/`-class terminal and a regular expression, or `}` and a template continuation.
-/

namespace Engine.Parse.Syntax

open Ecma.Grammar Search Lex

/-- The written production index of each syntactic alternative, by left-hand side and index. -/
def ctorTable : Thunk (Std.HashMap (Nat × Nat) Nat) := Thunk.mk fun _ =>
  prods.foldl (init := {}) fun m o => match o with
    | some p => if p.grammar == .syntactic then m.insert (p.rule.lhs.ctorIdx, p.alt) p.ctor else m
    | none => m

/-- §12.10's class of each `;`, by written production and right-hand side position. -/
def semiTable : Thunk (Std.HashMap (Nat × Nat) Semi) := Thunk.mk fun _ =>
  Gen.semis.foldl (init := {}) fun m s => m.insert (s.prod.ctorIdx, s.pos) s.semi

/-- A virtual `;` (`paren`: inserted after a `)`) may be the `;` at item `k` of `lhs`'s
alternative `alt`. -/
def virtualOk (lhs : NT) (alt k : Nat) (paren : Bool) : Bool :=
  match ctorTable.get[(lhs.ctorIdx, alt)]? >>= fun c => semiTable.get[(c, k)]? with
  | some .insertable | some .forHeaderIfDeclaration => !paren
  | some .doWhile => true
  | _ => false

/-- The lexical goal a lexical nonterminal is read under. -/
def goalOf (n : NT) : NT :=
  if n == .RegularExpressionLiteral then .InputElementRegExp
  else if n == .TemplateMiddle || n == .TemplateTail then .InputElementTemplateTail
  else .InputElementDiv

variable {N : Type} (B : Builder N) (cs : Array Nat) (first : Bool) (cx : Ctx) (stamp : Nat) (vs : Std.HashMap Nat Bool)

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

/-- A memo entry: the token `lexAtPure` reads at `p` under `goal`, or the leaf `n` from `s`, each
with its key. -/
inductive Memo where
  | tok (p : Nat) (goal : NT) (r : Lexed) (h : lexAtPure B cs first cx goal p = .ok r)
  | leaf (n : NT) (s : Nat) (r : Option Nat)
      (h : ∃ t, lexAtPure B cs first cx (goalOf n) (s / 2) = .ok t ∧ leafOf B cs cx n t = .ok r)

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

/-- A read at boundary `s`, for the memo entry in progress. -/
def note (s : Nat) : SM (Memo B cs first cx) Unit := modify fun st => { st with hzn := max st.hzn s }

/-- Boundary `s` was asked `bit`s: 1 a `/`-class terminal, 2 a regular expression, 4 `}`, 8 a template
continuation. -/
def ask (bit s : Nat) : SM (Memo B cs first cx) Unit :=
  if bit == 0 then pure () else
  modify fun st => { st with asks := st.asks.insert s (st.asks.getD s 0 ||| bit) }

/-- The bits of `ask` for terminal `str`. -/
def termBits (str : String) : Nat :=
  if str == "/" || str == "/=" then 1 else if str == "}" then 4 else 0

/-- The bits of `ask` for the lexical nonterminal `n`. -/
def leafBits (n : NT) : Nat :=
  if n == .RegularExpressionLiteral then 2
  else if n == .TemplateMiddle || n == .TemplateTail then 8
  else 0

/-- A virtual `;` waits at `s`. -/
def pending (s : Nat) : Bool := s % 2 == 0 && vs.contains (s / 2)

def textIs (t : Tok) (str : String) : Bool := (cs.extract t.i t.j).toList == str.toList.map Char.toNat

/-- Terminal `x` (item `k` of `lhs`'s alternative `alt`) from `s`. -/
def term (lhs : NT) (alt k : Nat) (x : Terminal) (s : Nat) : SM (Memo B cs first cx) (Option Nat) := do
  let .text str _ := x | return none
  note B cs first cx s
  if pending vs s then
    return if str == ";" && virtualOk lhs alt k (vs.getD (s / 2) false) then some (s + 1) else none
  ask B cs first cx (termBits str) s
  match ← lex B cs first cx .InputElementDiv (s / 2) with
  | .tok t => return if textIs cs t str then some (2 * t.j) else none
  | _ => return none

/-- The lexical nonterminal `n` as one token from `s`: the token's code points derive `n`. -/
def leaf (n : NT) (s : Nat) : SM (Memo B cs first cx) (Option Nat) := do
  note B cs first cx s
  if pending vs s then return none
  if s % 2 == 1 && goalOf n == .InputElementTemplateTail then
    throw (.unimplemented "a template continuation after an inserted `;`")
  ask B cs first cx (leafBits n) s
  let k := (n.ctorIdx, s)
  if let some (.leaf n' s' r _) := (← get).leaves[k]? then
    if n' = n ∧ s' = s then return r
  let ⟨t, ht⟩ ← lexP B cs first cx (goalOf n) (s / 2)
  match hr : leafOf B cs cx n t with
  | .ok r =>
    modify fun st => { st with leaves := st.leaves.insert k (.leaf n s r ⟨t, ht, hr⟩) }
    return r
  | .error e => throw e

/-- No line terminator before the token at `s` (a virtual `;` has none), from the trivia alone. -/
def noLT (s : Nat) : SM (Memo B cs first cx) Bool := do
  note B cs first cx s
  if pending vs s then return true
  let (k, lt) := skip B cs first cx (s / 2)
  return k ≥ cs.size || !lt

/-- The boundary a lookahead reads from `s`: past a waiting virtual `;`, no source token. -/
def look (s : Nat) : Nat := if pending vs s then s + 1 else s

/-- `look vs s`, noting a waiting virtual `;` read past. -/
def lookM (s : Nat) : SM (Memo B cs first cx) Nat := do
  if pending vs s then modify fun st => { st with spans := true }
  note B cs first cx (look vs s)
  return look vs s

/-- The source tokens from `s` start with the lookahead sequence. -/
def starts : List LookItem → Nat → SM (Memo B cs first cx) Bool
  | [], _ => pure true
  | .noLT :: rest, s => do
    if ← noLT B cs first cx vs (← lookM B cs first cx vs s) then starts rest s else pure false
  | .t x :: rest, s => do
    let .text str _ := x | return false
    match ← lex B cs first cx .InputElementDiv ((← lookM B cs first cx vs s) / 2) with
    | .tok t => if textIs cs t str then starts rest (2 * t.j) else pure false
    | _ => pure false

/-- The code point span of positions `lo` to `hi` (`Grammar.tokenSpan`): from the first token's
start to the last's end; an empty one at the next token's start, or at the end of the last. -/
def span (lo hi : Nat) : SM (Memo B cs first cx) (Nat × Nat) := do
  let (k, _) := skip B cs first cx (lo / 2)
  if hi / 2 > lo / 2 then return (k, hi / 2)
  return if k < cs.size then (k, k) else (lo / 2, lo / 2)

/-- The tokens' alphabet, with the virtual `;` before the code points `vs`. -/
def alpha : Alpha N (Memo B cs first cx) where
  g := .syntactic
  cx := cx
  term := term B cs first cx vs
  leaf := leaf B cs first cx vs
  phrase _ _ := pure none
  cond _ _ _ := pure false
  noLT := noLT B cs first cx vs
  starts := starts B cs first cx vs
  keep lhs n e := !(lhs == .ForStatement && n == .LexicalDeclaration && e % 2 == 1)
  keepAll lhs n := !(lhs == .ForStatement && n == .LexicalDeclaration)
  hit e := modify fun s => { s with far := max s.far e }
  span := span B cs first cx
  text lo hi := do let (i, j) ← span B cs first cx lo hi; return view cs i j
  leafNode n a b := do
    match ← lex B cs first cx (goalOf n) (a / 2) with
    | .tok t =>
      unless 2 * t.j == b do throw (.check "a leaf's span")
      match (Code.parse (T := Unit) B (cs.extract t.i t.j) .lexical cx t.i cs stamp n []).run'
          { steps := Code.budget (t.j - t.i) } with
      | .ok (some node) => pure node
      | .ok none => throw (.check "a leaf with no lexical derivation")
      | .error e => throw e
    | _ => throw (.check "a leaf without its token")
  negSpan _ _ _ _ := throw (.unimplemented "a negative item over a syntactic nonterminal")
  negAny _ _ := throw (.unimplemented "a lookahead over a syntactic nonterminal")

/-- The recursion depth bound over `n` code points: an expression nests a few dozen levels per
code point. -/
def depth (n : Nat) : Nat := 64 * n + 2000

/-- The steps a parse of `n` code points may take. -/
def budget (n : Nat) : Nat := 20000 * (n + 1)

/-- Where §12.10 inserts a virtual `;` when no parse reaches past `f`: the code point, and whether
only a do-while's `;` may take it; none when no rule applies. -/
def insertion (f : Nat) : SM (Memo B cs first cx) (Option (Nat × Bool)) := do
  if f % 2 == 1 || vs.contains (f / 2) then return none
  let p := f / 2
  match ← lex B cs first cx .InputElementDiv p with
  | .eof _ => return some (p, false)
  | .tok t =>
    if t.lt || textIs cs t "}" then return some (p, false)
    -- `f` is a token's end, so a `)` code point before it is the `)` token
    if 0 < p && cs[p - 1]? == some 0x29 then return some (p, true)
    return none
  | _ => return none

/-- The least boundary asked for both of a `/`-class terminal and a regular expression, or `}` and a
template continuation. -/
def bothAsked (asks : Std.HashMap Nat Nat) : Option Stop :=
  let both := asks.toArray.filter fun (_, m) => (m &&& 3) == 3 || (m &&& 12) == 12
  let least := both.foldl (init := none) fun acc (s, m) =>
    match acc with
    | some (s', _) => if s' ≤ s then acc else some (s, m)
    | none => some (s, m)
  match least with
  | some (s, m) =>
    some (.unimplemented s!"decline1 {if (m &&& 3) == 3 then "slash" else "brace"} at {s / 2}")
  | none => none

/-- Goal `goal` with parameters `ps` over the tokens of `cs` in context `cx`: its Parse Node, or none
when no parse exists. -/
def run (goal : NT) (ps : List Param) : Except Stop (Option N) := do
  let size := 2 * cs.size + 2
  let rec go : Nat → Std.HashMap Nat Bool → SM (Memo B cs (firstOf goal) cx) (Option N)
    | 0, _ => throw .fuel
    | fuel + 1, vs => do
      modify fun s => { s with far := 0, hzn := 0, active := ({}), reads := ({}), fwd := ({}) }
      let A := alpha B cs (firstOf goal) cx stamp vs
      let es ← finalEnds A size (depth cs.size) goal ps 0
      let mut done : Option Nat := none
      for e in es.toArray do
        if (skip B cs (firstOf goal) cx (e / 2)).1 ≥ cs.size && !pending vs e then done := some e
      if let some e := done then
        if vs.keys.any fun p => cs[(skip B cs (firstOf goal) cx p).1]? == some 0x2F then
          throw (.unimplemented "a `/` after an inserted `;`")
        if let some d := bothAsked (← get).asks then throw d
        let nd ← build A B size (depth cs.size) stamp (depth cs.size) goal ps 0 e
        unless B.nt nd == goal.ctorIdx do throw (.check "a node of another nonterminal")
        return some nd
      match ← insertion B cs (firstOf goal) cx vs (← get).far with
      | some (p, paren) =>
        if let some d := bothAsked (← get).asks then throw d
        modify (·.cut (2 * p))
        go fuel (vs.insert p paren)
      | none => return none
  (go (cs.size + 2) {}).run' { steps := budget cs.size }

end Engine.Parse.Syntax
