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
goal defined in several of them by each, |Pattern| among them. The grammar is the parse context's
(`Ctx`: Annex B's overlays in effect); a syntactic tree with a node of an overlay production for
non-strict code in strict mode code (`Strict.sloppyOk`) is no parse, the tree being the only one.
-/

namespace Engine.Parse

open Ecma.Grammar

variable {N : Type}

/-- Goal `goal` (a nonterminal's index) with arguments `args` over the code points `cs`, as
parser invocation `stamp`, under the grammar's rules as the readings `rd` replace them, in context
`cx`, `strict` its source text being strict mode code from outside, `lit` LookaheadSourceTokens read
literally (`Syntax.run`). -/
def parse (B : Builder N) (rd : List RuleReading) (cx : Ctx) (strict : Bool) (stamp : Nat) (cs : Array Nat)
    (goal : Nat) (args : List (Nat × Bool)) (lit : Bool := false) : Outcome N :=
  let ps := paramsOfArgs args
  let out (r : Except Stop (Option N)) : Outcome N := match r with
    | .ok (some n) => .ok n
    | .ok none => .noParse
    | .error s => .stop s
  if let some r := ruleTable.get[(GrammarId.syntactic.ctorIdx, goal)]? then
    match out (Syntax.run B cs cx stamp r.lhs ps lit) with
    | .ok n =>
      if !cx.annexB.any then .ok n
      else match Strict.sloppyOk B (Syntax.depth cs.size + 1) strict (Syntax.depth cs.size + 1) [] n with
        | some true => .ok n
        | some false => .noParse
        | none => .stop .depth
    | o => o
  else
    let gs := codeGrammars.filterMap fun g => (ruleTable.get[(g.ctorIdx, goal)]?).map ((g, ·))
    if gs.isEmpty then .stop (.unimplemented "a goal no grammar defines")
    else gs.foldl (init := .noParse) fun acc (g, r) => match acc with
      | .noParse => out (Code.run B cs g rd cx stamp r.lhs ps)
      | done => done

end Engine.Parse
