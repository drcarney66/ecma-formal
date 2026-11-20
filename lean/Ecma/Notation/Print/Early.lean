module

public import Ecma.Notation.Print
public import Ecma.Notation.Early

/-!
# Ecma print: Early Errors rules as spec.html's text

A rule's sentences on one line, joined by `Print.join`, laid out in its `<li>`: `row` prints the
content between `<li>` and `</li>` of one bullet of an Early Errors clause.
-/

@[expose] public section

namespace Ecma.Print.Early

open Ecma Ecma.Print

/-- A rule's exception. -/
def unlessOut (c : Ctx) : Option (UnlessForm × Cond) → Out
  | none => ([], "")
  | some (.plain, k) => cat [w "unless", cond c k]
  | some (.comma, k) => cat [w ",", w "unless", cond c k]
  | some (.optional, k) => cat [gw "<span normative-optional>", w ",", w "unless", cond c k, gw "</span>"]

mutual
/-- A sentence, ending with its full stop. -/
def sentence (c : Ctx) : EarlySentence → Out
  | .syntaxError e k u =>
    cat [words (if e then "It is an early Syntax Error if" else "It is a Syntax Error if"), cond c k, unlessOut c u, w "."]
  | .syntaxErrorIns k l => cat [words "It is a Syntax Error if", cond c k, w "<ins>", gw "and", cond c l, gw "</ins>", w "."]
  | .mustCover p t => cat [expr c p, words "must cover", ty c t, w "."]
  | .rulesApplied _ raw => cat [words "The Early Error rules for", w raw, words "are applied", w "."]
  | .ifInline k s => cat [w "If", cond c k, w ",", lowerFirst (sentence c s)]
  | .info s | .notApplied _ s | .forEachIn _ _ _ _ s | .stmt s => stmt c s
  | .layout raw _ => ([.raw raw false], "")
  | .readings _ lit _ => sentences c lit

/-- A rule's sentences, on one line. -/
def sentences (c : Ctx) : List EarlySentence → Out
  | [] => ([], "")
  | s :: r => cat [sentence c s, sentences c r]
end

/-- The context of a rule's sentences: its variables, no closure literal. -/
def rowCtx (d : Decls) (r : EarlyRow) : Ctx := { d, vars := r.vars, cl := #[], clos := #[], depth := 0 }

/-- Sentences as one line of text. -/
def text (c : Ctx) (ss : List EarlySentence) : String := join (sentences c ss).1

/-- A rule as spec.html has it: the content between `<li>` and `</li>`. -/
def row (d : Decls) (r : EarlyRow) : String :=
  let t := text (rowCtx d r) r.body
  match r.layout with
  | .block => "\n" ++ spaces (r.indent + 2) ++ t ++ "\n" ++ spaces r.indent
  | _ => t

end Ecma.Print.Early
