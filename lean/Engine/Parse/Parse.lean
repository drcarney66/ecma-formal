module

public import Engine.Parse.Syntax
public import Engine.Parse.Check
public import Engine.Parse.Strict

@[expose] public section

/-!
# ParseText's parse: a goal symbol over code points

`parse` gives the Parse Node of the code points `cs` as an instance of goal `goal` with the
parameters its arguments set, built through the builder; "no parse" only after a complete
decision of the grammar; otherwise a stop. The syntactic goals are decided over tokens
(`Syntax`), the code point grammars (lexical, numeric string, RegExp, JSON) over code points (`Code`), a
goal defined in several of them by each, |Pattern| among them. A goal no grammar defines has no
parse (`GrammarCtx.Parses` is `False`).
-/

namespace Engine.Parse

open Ecma.Grammar

variable {N : Type}

/-- Goal `goal` (a nonterminal's index) with arguments `args` over the code points `cs`, as
parser invocation `stamp`, in context `cx`, `strict` its source text being strict mode code from
outside (`Syntax.run`). -/
def parse (B : Builder N) (cx : Ctx) (strict : Bool) (stamp : Nat) (cs : Array Nat)
    (goal : Nat) (args : List (Nat × Bool)) : Outcome N :=
  let ps := paramsOfArgs args
  let out (r : Except Stop (Option N)) : Outcome N := match r with
    | .ok (some n) => .ok n
    | .ok none => .noParse
    | .error s => .stop s
  if let some lhs := ruleNt .syntactic goal then
    match out (Syntax.run B cs cx stamp lhs ps) with
    | .ok n =>
      if !cx.annexB.any then .ok n
      else match Strict.sloppyOk B (Syntax.depth cs.size + 1) strict (Syntax.depth cs.size + 1) [] n with
        | some true => .ok n
        | some false => .noParse
        | none => .stop .depth
    | o => o
  else
    let gs := codeGrammars.filterMap fun g => (ruleNt g goal).map ((g, ·))
    gs.foldl (init := .noParse) fun acc (g, lhs) => match acc with
      | .noParse => out (Code.run B cs g cx stamp lhs ps)
      | done => done

end Engine.Parse
