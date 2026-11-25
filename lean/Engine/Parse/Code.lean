module

public import Engine.Parse.Search

@[expose] public section

/-!
# The code point grammars

The lexical, numeric string and RegExp grammars over code points (`Ecma.Grammar.codeAlphabet`): a
terminal is its code points (`<USP>` the builder's class), a descriptive phrase one code point of
its class, a `[> but only if …]` condition the MV of the node before it, and
`[no LineTerminator here]` always holds. `run` decides a goal over the whole input by the search;
its nodes' spans are offset by `off`, for a token's lexical derivation inside a larger text.
Where B.1.2 orders the grammar (RegExp under Annex B), `run` gives the committed parse in two passes,
as `Ecma.Grammar.groupCond` reads the group-number condition: the Pattern with the condition true,
then the goal with CapturingGroupNumber at most that tree's left-capturing parentheses.
-/

namespace Engine.Parse.Code

open Ecma.Grammar Search

variable {N T : Type}

/-- The end of terminal `x` at `h`, if the input matches it there. -/
def termEnd (B : Builder N) (cs : Array Nat) (x : Terminal) (h : Nat) : Option Nat :=
  match x with
  | .text s _ =>
    let w := s.toList.map Char.toNat
    if h + w.length ≤ cs.size && (cs.extract h (h + w.length)).toList == w then some (h + w.length) else none
  | .cp n => cs[h]? >>= fun c => match n.codePoint with
    | some v => if c == v then some (h + 1) else none
    | none => if B.usp c then some (h + 1) else none

def isAsciiLetter (c : Nat) : Bool := (0x41 ≤ c && c ≤ 0x5A) || (0x61 ≤ c && c ≤ 0x7A)

/-- A WhiteSpace or LineTerminator code point beyond ASCII: never ID_Start or ID_Continue. -/
def isSpaceAbove (B : Builder N) (c : Nat) : Bool := c == 0xFEFF || c == 0x2028 || c == 0x2029 || B.usp c

/-- A descriptive phrase's class holds of code point `c`. -/
def phraseOk (B : Builder N) (p : Phrase) (c : Nat) : Except Stop Bool :=
  match p with
  | .anyCodePoint => pure (c ≤ 0x10FFFF)
  | .idStart => match B.idStart with
    | some f => pure (f c)
    | none =>
      if c < 0x80 then pure (isAsciiLetter c)
      else if isSpaceAbove B c then pure false
      else throw .nonAsciiId
  | .idContinue => match B.idContinue with
    | some f => pure (f c)
    | none =>
      if c < 0x80 then pure (isAsciiLetter c || (0x30 ≤ c && c ≤ 0x39) || c == 0x5F)
      else if isSpaceAbove B c then pure false
      else throw .nonAsciiId
  | .leadSurrogate => pure (0xD800 ≤ c && c ≤ 0xDBFF)
  | .trailSurrogate => pure (0xDC00 ≤ c && c ≤ 0xDFFF)
  | _ => throw (.check "a condition as a phrase")

/-- The MV of the hexadecimal digits `a` to `b` (§12.9.3; a NumericLiteralSeparator adds none). -/
def hexMV (cs : Array Nat) (a b : Nat) : Except Stop Nat :=
  (cs.extract a b).foldlM (init := 0) fun v c =>
    if 0x30 ≤ c && c ≤ 0x39 then pure (v * 16 + (c - 0x30))
    else if 0x61 ≤ c && c ≤ 0x66 then pure (v * 16 + (c - 0x61 + 10))
    else if 0x41 ≤ c && c ≤ 0x46 then pure (v * 16 + (c - 0x41 + 10))
    else if c == 0x5F then pure v
    else throw (.check "MV of a non-digit")

/-- A `[> but only if …]` condition holds of the node over `a` to `b` before it. -/
def condOk (cs : Array Nat) (p : Phrase) (a b : Nat) : Except Stop Bool := do
  match p with
  | .mvAbove10FFFF => return (← hexMV cs a b) > 0x10FFFF
  | .mvAtMost10FFFF => return (← hexMV cs a b) ≤ 0x10FFFF
  | .mvLead => let v ← hexMV cs a b; return 0xD800 ≤ v && v ≤ 0xDBFF
  | .mvTrail => let v ← hexMV cs a b; return 0xDC00 ≤ v && v ≤ 0xDFFF
  | .mvNonSurrogate => let v ← hexMV cs a b; return !(0xD800 ≤ v && v ≤ 0xDFFF)
  | .groupNumberAtMostCount => throw (.unimplemented "B.1.2's group number condition")
  | _ => throw (.check "a phrase as a condition")

/-- §22.2.1.5 CapturingGroupNumber: the MV of the decimal digits `a` to `b`. -/
def decimalMV (cs : Array Nat) (a b : Nat) : Nat := (cs.extract a b).foldl (fun v c => 10 * v + (c - 0x30)) 0

/-- `condOk`, B.1.2's group-number condition `grp` of the CapturingGroupNumber where given. -/
def condAt (grp : Option (Nat → Bool)) (cs : Array Nat) (p : Phrase) (a b : Nat) : Except Stop Bool :=
  match grp with
  | none => condOk cs p a b
  | some f => match p with
    | .groupNumberAtMostCount => pure (f (decimalMV cs a b))
    | _ => condOk cs p a b

/-- The input from `j` starts with the lookahead sequence. -/
def startsWith (B : Builder N) (cs : Array Nat) : List LookItem → Nat → Bool
  | [], _ => true
  | .t x :: rest, j => match termEnd B cs x j with
    | some h => j < h && startsWith B cs rest h
    | none => false
  | .noLT :: rest, j => startsWith B cs rest j

/-- Items `is` under `ps` derive exactly the code points `i` to `h`, nonterminals decided by `rec`;
an item that is negative, or a condition, is a stop. -/
def decSeq (B : Builder N) (cs : Array Nat) (rec : NT → List Param → Nat → Nat → Except Stop Bool)
    (ps : List Param) : List Item → Nat → Nat → Except Stop Bool
  | [], i, h => pure (i == h)
  | .sym (.t x) o :: is, i, h => do
    let absent ← if o then decSeq B cs rec ps is i h else pure false
    if absent then pure true
    else match termEnd B cs x i with
      | some j => if j ≤ h then decSeq B cs rec ps is j h else pure false
      | none => pure false
  | .sym (.nt m args) o :: is, i, h => do
    let absent ← if o then decSeq B cs rec ps is i h else pure false
    if absent then pure true
    else (List.range (h + 1 - i)).anyM fun d => do
      if ← rec m (applyArgs ps args) i (i + d) then decSeq B cs rec ps is (i + d) h else pure false
  | .phrase p :: is, i, h => match cs[i]? with
    | some c => do if (← phraseOk B p c) && i + 1 ≤ h then decSeq B cs rec ps is (i + 1) h else pure false
    | none => pure false
  | .empty :: is, i, h => decSeq B cs rec ps is i h
  | .noLT :: is, i, h => decSeq B cs rec ps is i h
  | _ :: _, _, _ => throw (.unimplemented "a negative item or a condition inside a negative item")

/-- A negative item's nonterminal `n` under `ps` derives exactly the code points `i` to `h` in
grammar `g` in context `cx`, within `fuel` levels: an exhaustive search over the splits. -/
def dec (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx) :
    Nat → NT → List Param → Nat → Nat → Except Stop Bool
  | 0, _, _, _, _ => throw .depth
  | f + 1, n, ps, i, h => do
    let some es := effAlts g cx n.ctorIdx | return false
    es.anyM fun e =>
      if e.alt.guard.all (Guard.holds ps) then decSeq B cs (dec B cs g cx f) ps e.alt.rhs i h else pure false

/-- A lookahead's nonterminal `n` derives some code points from `i`: one of its terminals starts
there (a nonterminal not a set of terminals is a stop). -/
def decAny (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx) (n : NT) (i : Nat) :
    Except Stop Bool := do
  let some es := effAlts g cx n.ctorIdx | return false
  es.anyM fun e => match e.alt.guard, e.alt.rhs with
    | [], [.sym (.t x) false] => pure (termEnd B cs x i).isSome
    | _, _ => throw (.unimplemented "a lookahead nonterminal that is not a set of terminals")

/-- The code point alphabet of grammar `g` in context `cx` over `cs`, its spans
offset by `off`, its texts views of `src` at those spans, B.1.2's group-number condition `grp`. -/
def alpha (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx) (off : Nat := 0)
    (src : Array Nat := cs) (grp : Option (Nat → Bool) := none) : Alpha N T where
  g := g
  cx := cx
  term _ _ _ x p := pure (termEnd B cs x p)
  leaf _ _ := pure none
  phrase ph p := match cs[p]? with
    | some c => do return if ← liftE (phraseOk B ph c) then some (p + 1) else none
    | none => pure none
  cond c a b := liftE (condAt grp cs c a b)
  noLT _ := pure true
  starts q j := pure (startsWith B cs q j)
  keep _ _ _ := true
  keepAll _ _ := true
  hit _ := pure ()
  span a b := pure (off + a, off + b)
  text a b := pure (view src (off + a) (off + b))
  leafNode _ _ _ := throw (.check "a leaf in a code point grammar")
  negSpan n ps a b := liftE (dec B cs g cx 64 n ps a b)
  negAny n a := liftE (decAny B cs g cx n a)

/-- The recursion depth bound over `n` code points: a list nests once per element, a group a few
levels per code point. -/
def depth (n : Nat) : Nat := 8 * n + 1000

/-- The steps a search of `n` code points may take. -/
def budget (n : Nat) : Nat := 4096 * (n + 1)

/-- Goal `n` with parameters `ps` over the whole input `cs` of grammar `g` in
context `cx`, the group-number condition `grp`: its Parse Node (spans offset by `off`, texts views of `src`),
or none when the search finds no derivation. -/
def parse (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx) (off : Nat)
    (src : Array Nat) (stamp : Nat) (n : NT) (ps : List Param) (grp : Option (Nat → Bool) := none) :
    SM T (Option N) := do
  let A : Alpha N T := alpha B cs g cx off src grp
  let es ← finalEnds A cs.size (depth cs.size) n ps 0
  unless es.mem cs.size do return none
  let nd ← build A B cs.size (depth cs.size) stamp (depth cs.size) n ps 0 cs.size
  unless B.nt nd == n.ctorIdx do throw (.check "a node of another nonterminal")
  return some nd

/-- The left-capturing parentheses (`capturingTable`) of the tree `nd`, within depth `d`. -/
def countCapturing (B : Builder N) : Nat → N → Except Stop Nat
  | 0, _ => throw .depth
  | d + 1, nd => ((B.kids nd).toList.filterMap (·.2)).foldlM (init := if capturingTable.get.contains (B.prod nd) then 1 else 0)
      fun a k => return a + (← countCapturing B d k)

/-- `parse` from a fresh state, the group-number condition `grp`. -/
def runWith (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx) (stamp : Nat) (n : NT)
    (ps : List Param) (grp : Option (Nat → Bool)) : Except Stop (Option N) :=
  (parse (T := Unit) B cs g cx 0 cs stamp n ps grp).run' { steps := budget cs.size }

/-- B.1.2's group-number condition, stratified (`Ecma.Grammar.groupCond`): CapturingGroupNumber at most
the left-capturing parentheses of the committed Pattern[~UnicodeMode, ~UnicodeSetsMode,
~NamedCaptureGroups] over `cs` with the condition true; false without one. -/
def groupLimit (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx) :
    Except Stop (Nat → Bool) := do
  match ← runWith B cs g cx 0 .Pattern [] (some fun _ => true) with
  | some t => let k ← countCapturing B (depth cs.size) t; return (· ≤ k)
  | none => return fun _ => false

/-- `parse` from a fresh state; where B.1.2 orders `g`, the committed parse with the group-number
condition `groupLimit`. -/
def run (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx) (stamp : Nat) (n : NT)
    (ps : List Param) : Except Stop (Option N) :=
  if (orderedIn cx g).isEmpty then (parse (T := Unit) B cs g cx 0 cs stamp n ps).run' { steps := budget cs.size }
  else do runWith B cs g cx stamp n ps (some (← groupLimit B cs g cx))

end Engine.Parse.Code
