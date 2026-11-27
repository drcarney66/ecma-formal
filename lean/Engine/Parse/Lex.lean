module

public import Engine.Parse.Code

@[expose] public section

/-!
# The lexer: `lexAt`

`lexAt first goal i` reads the input elements from `i` under the lexical goal the parser chose (§12;
with `first`, the input of a Script or Module, its first element is read under
InputElementHashbangOrRegExp): white space, line terminators and comments (and then a
HashbangComment at the start) are skipped, recording whether one of them is a line terminator for
the syntactic grammar (`Element.breaks`); then the token is the longest sequence of code points one
of the goal's token classes derives, each class decided by the code point search over the whole
input, and its Parse Node built by the search (`lexAtPure`: on a state of its own). A NumericLiteral
whose next code point, by itself, is an IdentifierStart or a DecimalDigit is rejected by §12.9.3's
follow rule.
-/

namespace Engine.Parse.Lex

open Ecma.Grammar Search

/-- A token: its code points `i` to `j`, the lexical nonterminal it is an instance of, and
whether a line terminator precedes it. -/
structure Tok where
  i : Nat
  j : Nat
  cls : NT
  lt : Bool
  deriving Inhabited

/-- What `lexAt` reads: a token; the end of the input, after the trivia; code points no token of
the goal derives; or a NumericLiteral that §12.9.3's follow rule rejects. -/
inductive Lexed where
  | tok (t : Tok)
  | eof (lt : Bool)
  | bad (pos : Nat)
  | follow (pos : Nat)
  deriving Inhabited

/-- The goal's first input element is read under InputElementHashbangOrRegExp. -/
def firstOf (goal : NT) : Bool := goal == .Script || goal == .Module

def isLT (c : Nat) : Bool := c == 0xA || c == 0xD || c == 0x2028 || c == 0x2029

variable {N T : Type} (B : Builder N) (cs : Array Nat) (first : Bool)

/-- A WhiteSpace code point. -/
def isWS (c : Nat) : Bool := c == 0x9 || c == 0xB || c == 0xC || c == 0xFEFF || B.usp c

/-- The first line terminator from `k`, or the end of the input. -/
def lineEnd (k : Nat) : Nat :=
  if h : k < cs.size then if isLT cs[k] then k else lineEnd (k + 1) else cs.size
termination_by cs.size - k

/-- The first `*/` from `k`: the position of its `*`. -/
def closeAt (k : Nat) : Option Nat :=
  if h : k + 1 < cs.size then if cs[k] == 0x2A && cs[k + 1] == 0x2F then some k else closeAt (k + 1) else none
termination_by cs.size - k

/-- The end of the comment at `i` and whether it holds a line terminator; none if no comment
starts there. A HashbangComment is one only at 0 with `first`. A MultiLineComment ends at its first `*/`. -/
def comment (i : Nat) : Option (Nat × Bool) :=
  match cs[i]?, cs[i + 1]? with
  | some 0x2F, some 0x2F => some (lineEnd cs (i + 2), false)
  | some 0x23, some 0x21 => if first && i == 0 then some (lineEnd cs (i + 2), false) else none
  | some 0x2F, some 0x2A => (closeAt cs (i + 2)).map fun c => (c + 2, (cs.extract (i + 2) c).any isLT)
  | _, _ => none

/-- The first code point from `k` that is not WhiteSpace, or the end. -/
def wsEnd (k : Nat) : Nat :=
  if h : k < cs.size then if isWS B cs[k] then wsEnd (k + 1) else k else k
termination_by cs.size - k

/-- The end of B.1.1's HTMLCloseComment at `k`, the end of its line; none if none starts there. -/
def htmlClose (k : Nat) : Option Nat :=
  let w := wsEnd B cs k
  match cs[w]?, cs[w + 1]?, cs[w + 2]? with
  | some 0x2D, some 0x2D, some 0x3E => some (lineEnd cs (w + 3))
  | some 0x2F, some 0x2A, _ => match closeAt cs (w + 2) with
    | some c =>
      if (cs.extract (w + 2) c).any isLT then none
      else if h : k < c + 2 ∧ c + 2 ≤ cs.size then htmlClose (c + 2) else none
    | none => none
  | _, _, _ => none
termination_by cs.size - k

variable (cx : Ctx)

/-- B.1.1's HTML-like comments are in effect (Annex B `htmlLikeComments`, not a |Module|). -/
def html : Bool := cx.annexB.has .htmlLikeComments && !cx.module

/-- B.1.1's comment at `k`, its end and whether it holds a line terminator; none if none starts
there or B.1.1 is not in effect. -/
def htmlAt (k : Nat) : Option (Nat × Bool) :=
  if !html cx then none
  else
    let open1 := if first && k == 0 then (htmlClose B cs 0).map (·, false) else none
    open1 <|> match cs[k]?, cs[k + 1]?, cs[k + 2]?, cs[k + 3]? with
    | some 0x3C, some 0x21, some 0x2D, some 0x2D => some (lineEnd cs (k + 4), false)
    | some 0x2F, some 0x2A, _, _ => (closeAt cs (k + 2)).bind fun c =>
      if (cs.extract (k + 2) c).any isLT then (htmlClose B cs (c + 2)).map (·, true) else none
    | some c, n, _, _ =>
      if isLT c then (htmlClose B cs (if c == 0xD && n == some 0xA then k + 2 else k + 1)).map (·, true) else none
    | none, _, _, _ => none

/-- The trivia from `k`, within `fuel` elements. -/
def skipFrom : Nat → Nat → Bool → Nat × Bool
  | 0, k, lt => (k, lt)
  | f + 1, k, lt => match cs[k]? with
    | none => (k, lt)
    | some c => match htmlAt B cs first cx k with
      | some (e, l) => skipFrom f e (lt || l)
      | none =>
        if isWS B c then skipFrom f (k + 1) lt
        else if isLT c then skipFrom f (k + 1) true
        else match comment cs first k with
          | some (e, l) => skipFrom f e (lt || l)
          | none => (k, lt)

/-- The trivia from `i`: where the next token may start, and whether a line terminator precedes it. -/
def skip (i : Nat) : Nat × Bool := skipFrom B cs first cx (cs.size - i + 1) i false

/-- The token classes of a lexical goal, finer than its alternatives. -/
def classes (goal : NT) : List NT :=
  let common : List NT := [.IdentifierName, .PrivateIdentifier, .Punctuator, .NumericLiteral, .StringLiteral,
    .NoSubstitutionTemplate, .TemplateHead]
  common ++ match goal with
  | .InputElementDiv => [.DivPunctuator, .RightBracePunctuator]
  | .InputElementRegExp => [.RightBracePunctuator, .RegularExpressionLiteral]
  | .InputElementRegExpOrTemplateTail => [.RegularExpressionLiteral, .TemplateMiddle, .TemplateTail]
  | .InputElementTemplateTail => [.DivPunctuator, .TemplateMiddle, .TemplateTail]
  | _ => [.RegularExpressionLiteral]

/-- The furthest end of each class. -/
def furthest (found : List (NT × Nat)) (k : Nat) : Nat := found.foldl (fun m e => max m e.2) k

/-- Each class of `goal` from `k`, with its furthest end (`k` when it has none). -/
def lexFound (goal : NT) (k : Nat) : SM T (List (NT × Nat)) :=
  (classes goal).mapM fun c => do
    return (c, (← finalEnds (Code.alpha B cs .lexical cx) cs.size (Code.depth cs.size) c [] k).maxFrom k)

/-- `lexAt first goal i`: the next token from `i` under lexical goal `goal`. -/
def lexAt (goal : NT) (i : Nat) : SM T Lexed := do
  let A : Alpha N T := Code.alpha B cs .lexical cx
  let (k, lt) := skip B cs first cx i
  if k ≥ cs.size then return .eof lt
  let found ← lexFound (T := T) B cs cx (if first && k == 0 then .InputElementHashbangOrRegExp else goal) k
  let j := furthest found k
  if j == k then return .bad k
  if j > cs.size then throw (.check "a token past the input")
  let some (cls, _) := found.find? (·.2 == j) | return .bad k
  if (found.filter (·.2 == j)).length > 1 then throw (.check "two token classes of one length")
  let nd ← build A B cs.size (Code.depth cs.size) 0 (Code.depth cs.size) cls [] k j
  unless B.nt nd == cls.ctorIdx do throw (.check "a token's node of another nonterminal")
  if cls == .NumericLiteral then
    if let some c := cs[j]? then
      if (0x30 ≤ c && c ≤ 0x39) || Code.dec B cs .lexical cx 16 .IdentifierStart [] j (j + 1) then
        return .follow j
  return .tok ⟨k, j, cls, lt⟩

/-- `lexAt` from a fresh state. -/
def lexAtPure (goal : NT) (i : Nat) : Except Stop Lexed :=
  (lexAt (T := Unit) B cs first cx goal i).run' { steps := Code.budget cs.size }

end Engine.Parse.Lex
