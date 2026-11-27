module

public import Engine.Parse.Search
public import Ecma.Grammar.Derives

@[expose] public section

/-!
# The code point grammars

The lexical, numeric string, RegExp and JSON grammars over code points (`Ecma.Grammar.codeAlphabet`): a
terminal is its code points (`<USP>` the builder's class), a descriptive phrase one code point of
its class, a `[> but only if …]` condition the MV of the node before it (`Grammar.hexMV`), and
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
    if 0 < w.length && h + w.length ≤ cs.size && (cs.extract h (h + w.length)).toList == w then some (h + w.length) else none
  | .cp n => cs[h]? >>= fun c => match n.codePoint with
    | some v => if c == v then some (h + 1) else none
    | none => if B.usp c then some (h + 1) else none

/-- A descriptive phrase's class holds of code point `c`. -/
def phraseOk (B : Builder N) (p : Phrase) (c : Nat) : Bool :=
  match p with
  | .anyCodePoint => c ≤ 0x10FFFF
  | .idStart => B.idStart c
  | .idContinue => B.idContinue c
  | .leadSurrogate => 0xD800 ≤ c && c ≤ 0xDBFF
  | .trailSurrogate => 0xDC00 ≤ c && c ≤ 0xDFFF
  | _ => false

/-- A `[> but only if …]` condition holds of the node over `a` to `b` before it (`Grammar.hexMV`). -/
def condOk (cs : Array Nat) (p : Phrase) (a b : Nat) : Bool :=
  let s := (cs.extract a b).toList
  match p with
  | .mvAbove10FFFF => (Ecma.Grammar.hexMV s).any (· > 0x10FFFF)
  | .mvAtMost10FFFF => (Ecma.Grammar.hexMV s).any (· ≤ 0x10FFFF)
  | .mvLead => (Ecma.Grammar.hexMV s).any fun v => 0xD800 ≤ v && v ≤ 0xDBFF
  | .mvTrail => (Ecma.Grammar.hexMV s).any fun v => 0xDC00 ≤ v && v ≤ 0xDFFF
  | .mvNonSurrogate => (Ecma.Grammar.hexMV s).any fun v => !(0xD800 ≤ v && v ≤ 0xDFFF)
  | _ => false

/-- §22.2.1.5 CapturingGroupNumber: the MV of the decimal digits `a` to `b`. -/
def decimalMV (cs : Array Nat) (a b : Nat) : Nat := Ecma.Grammar.decimalMV (cs.extract a b).toList

/-- `condOk`, B.1.2's group-number condition `grp` of the CapturingGroupNumber where given. -/
def condAt (grp : Option (Nat → Bool)) (cs : Array Nat) (p : Phrase) (a b : Nat) : Bool :=
  match grp with
  | none => condOk cs p a b
  | some f => match p with
    | .groupNumberAtMostCount => f (decimalMV cs a b)
    | _ => condOk cs p a b

/-- The input from `j` starts with the lookahead sequence. -/
def startsWith (B : Builder N) (cs : Array Nat) : List LookItem → Nat → Bool
  | [], _ => true
  | .t x :: rest, j => match termEnd B cs x j with
    | some h => j < h && startsWith B cs rest h
    | none => false
  | .noLT :: rest, j => startsWith B cs rest j

/-- Items `is` under `ps` derive exactly the code points `i` to `h`, nonterminals decided by `rec`. -/
def decSeq (B : Builder N) (cs : Array Nat) (rec : NT → List Param → Nat → Nat → Bool)
    (ps : List Param) : List Item → Nat → Nat → Bool
  | [], i, h => i == h
  | .sym (.t x) o :: is, i, h =>
    (o && decSeq B cs rec ps is i h) || match termEnd B cs x i with
      | some j => j ≤ h && decSeq B cs rec ps is j h
      | none => false
  | .sym (.nt m args) o :: is, i, h =>
    (o && decSeq B cs rec ps is i h) || (List.range (h + 1 - i)).any fun d =>
      rec m (applyArgs ps args) i (i + d) && decSeq B cs rec ps is (i + d) h
  | .phrase p :: is, i, h => match cs[i]? with
    | some c => phraseOk B p c && i + 1 ≤ h && decSeq B cs rec ps is (i + 1) h
    | none => false
  | .empty :: is, i, h => decSeq B cs rec ps is i h
  | .noLT :: is, i, h => decSeq B cs rec ps is i h
  | _ :: _, _, _ => false

/-- A negative item's nonterminal `n` under `ps` derives exactly the code points `i` to `h` in
grammar `g` in context `cx`, within `fuel` levels (`posBounded`). -/
def dec (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx) :
    Nat → NT → List Param → Nat → Nat → Bool
  | 0, _, _, _, _ => false
  | f + 1, n, ps, i, h =>
    (altsOf cx g n).any fun e =>
      e.alt.guard.all (Guard.holds ps) && decSeq B cs (dec B cs g cx f) ps e.alt.rhs i h

/-- A lookahead's nonterminal `n` derives some code points from `i`: one of its terminals starts there. -/
def decAny (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx) (n : NT) (i : Nat) : Bool :=
  (altsOf cx g n).any fun e => match e.alt.guard, e.alt.rhs with
    | [], [.sym (.t x) false] => (termEnd B cs x i).isSome
    | _, _ => false

/-- The code point alphabet of grammar `g` in context `cx` over `cs`, its spans
offset by `off`, its texts views of `src` at those spans, B.1.2's group-number condition `grp`. -/
def alpha (B : Builder N) (cs : Array Nat) (g : GrammarId) (cx : Ctx) (off : Nat := 0)
    (src : Array Nat := cs) (grp : Option (Nat → Bool) := none) : Alpha N T where
  g := g
  cx := cx
  term _ _ x p := pure (termEnd B cs x p)
  leaf _ _ := pure none
  phrase ph p := match cs[p]? with
    | some c => pure (if phraseOk B ph c then some (p + 1) else none)
    | none => pure none
  cond c a b := pure (condAt grp cs c a b)
  noLT _ := pure true
  starts q j := pure (startsWith B cs q j)
  keep _ _ _ := true
  keepAll _ _ := true
  hit e := modify fun s => { s with far := max s.far e }
  span a b := pure (off + a, off + b)
  text a b := pure (view src (off + a) (off + b))
  leafNode _ _ _ := throw (.check "a leaf in a code point grammar")
  negSpan n ps a b := pure (dec B cs g cx 16 n ps a b)
  negAny n a := pure (decAny B cs g cx n a)

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

/-- The left-capturing parentheses (`isCapturing`) of the tree `nd`, within depth `d`. -/
def countCapturing (B : Builder N) : Nat → N → Except Stop Nat
  | 0, _ => throw .depth
  | d + 1, nd => ((B.kids nd).toList.filterMap (·.2)).foldlM (init := if isCapturing (B.prod nd) then 1 else 0)
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
  if !orderedBy cx g then (parse (T := Unit) B cs g cx 0 cs stamp n ps).run' { steps := budget cs.size }
  else do runWith B cs g cx stamp n ps (some (← groupLimit B cs g cx))

end Engine.Parse.Code
