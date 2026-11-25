module

public import Ecma.Grammar.Print
public import Ecma.Grammar.Gen.Index
public import Ecma.Notation.Syntax

/-!
# Canonical SpecTec printers for ECMA-262 tokens and grammar files

Shared lexical token formatters (`Ecma.SpecTec`) plus byte-for-byte printers for
`01-grammar-*.spectec`..`06-grammar-*.spectec` and `07-grammar-index.spectec`.
All functions are structurally recursive and match `crates/spectec/src/print.rs`.
-/

@[expose] public section

namespace Ecma.SpecTec

def keywords : Array String := #[
  "alg", "and", "annot", "anyCodePoint", "assert", "assert_if", "block", "butnot", "by", "call_at",
  "captures", "checked_jobs", "child", "child_of", "children", "choice", "clause", "clause_prods",
  "clause_props", "closure", "cmethod", "code", "completion", "component", "cover", "cp", "cu", "data",
  "def", "default", "defined", "desc", "dfn", "do", "doc", "early", "early_syntax_error", "either", "else",
  "else_if", "empty", "enum", "eq", "err", "excl", "extern", "fails", "false", "field", "fields",
  "for_children", "for_children_of", "for_each", "for_each_rec", "for_index", "for_keys", "for_range",
  "form", "frac", "from", "goal", "grammar", "grammar_alt", "groupNumberAtMostCount", "header", "hex",
  "idContinue", "idStart", "if", "if_else", "if_inline", "imethod", "in", "incl", "info", "init",
  "interval", "intrinsic", "is", "keys", "kind", "leadSurrogate", "let", "lines", "link", "list",
  "lookahead", "many", "math", "method", "modulo", "must_cover", "mvAbove10FFFF", "mvAtMost10FFFF",
  "mvLead", "mvNonSurrogate", "mvTrail", "nan", "nan_f", "nan_z", "neg", "neither", "new",
  "new_target", "no", "noLT", "none", "not", "not_applied", "not_in", "note", "nt", "null", "num",
  "num_f", "num_n", "num_z", "obj", "of", "one", "one_of", "onlyIf", "op", "opt", "or", "order",
  "param", "params", "pass", "perform", "plain", "plus", "pred", "prods", "props", "push", "raw",
  "realm", "record", "ref", "remove", "remove_restore", "repeat", "repeat_n", "repeat_until",
  "repeat_while", "rest", "resume", "resume_let", "resume_top", "resumed_with", "ret", "retired",
  "return", "rev", "row", "rows", "rule", "rules_applied", "sat", "schema", "sdo", "sdo_row", "semi", "seq",
  "set", "set_code_state", "sig", "slot", "slots", "some", "sort", "sort_alias", "step", "steps", "stmt", "subject", "super", "supplemental", "suspend", "symbols", "syntax", "syntax_error",
  "syntax_error_ins", "table", "table_step", "test", "text", "that", "thead", "then", "this",
  "this_node", "this_value", "throw", "times", "to", "trailSurrogate", "true", "ty", "undefined",
  "unless", "unreachable", "val", "var", "vars", "where"
]

def bsearchKw (s : String) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if lo ≥ hi then false
    else
      let mid := (lo + hi) / 2
      let k := keywords.getD mid ""
      if s == k then true
      else if s < k then bsearchKw s fuel lo mid
      else bsearchKw s fuel (mid + 1) hi

def isKeyword (s : String) : Bool := bsearchKw s keywords.size 0 keywords.size

def isIdentStart (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

def isIdentCont (c : Char) : Bool :=
  isIdentStart c || ('0' ≤ c && c ≤ '9')

def isPrimStart (c : Char) : Bool :=
  isIdentStart c || c == '𝔽' || c == 'ℝ' || c == 'ℤ'

def isPrimCont (c : Char) : Bool :=
  isIdentCont c || c == '𝔽' || c == 'ℝ' || c == 'ℤ'

def isClauseChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.' || c == '%' || c == '/'

def escChar (c : Char) : String :=
  if c == '\\' then "\\\\"
  else if c == '"' then "\\\""
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c.toNat < 32 || c.toNat == 127 then
    let hex := String.ofList ((Nat.toDigits 16 c.toNat).map Char.toLower)
    "\\u{" ++ hex ++ "}"
  else c.toString

def escStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map escChar) ++ "\""

def tokIdent (s : String) : String :=
  match s.toList with
  | c :: cs => if isIdentStart c && cs.all isIdentCont && !isKeyword s then s else "#" ++ escStr s
  | [] => "#" ++ escStr s

def tokPrim (s : String) : String :=
  match s.toList with
  | c :: cs => if isPrimStart c && cs.all isPrimCont && !isKeyword s then "$" ++ s else "$" ++ escStr s
  | [] => "$" ++ escStr s

def tokClause (s : String) : String :=
  if !s.isEmpty && s.toList.all isClauseChar then "@" ++ s else "@" ++ escStr s

def nameAt (a : Array String) (i : Nat) : String := a.getD i ""

def tokAlgRef (d : Decls) (a : AlgId) : String :=
  let cl := tokClause (nameAt d.clauses a.clause)
  if a.idx == 0 then cl else cl ++ "#" ++ toString a.idx

def tokField (s : String) : String := "[[" ++ s ++ "]]"

def tokEnum (s : String) : String := "~" ++ s ++ "~"

def tokProd (s : String) : String := "p" ++ escStr s

def tokTable (s : String) : String := "t" ++ escStr s

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

end Ecma.SpecTec

namespace Ecma.Grammar.PrintSpecTec

open Ecma Ecma.Grammar Ecma.SpecTec

def grammarName : GrammarId → String
  | .numericString => "numericString"
  | .lexical => "lexical"
  | .syntactic => "syntactic"
  | .regExp => "regExp"
  | .annexB => "annexB"
  | .json => "json"

def printTerminal : Terminal → String
  | .text s false => escStr s
  | .text s true => "alt " ++ escStr s
  | .cp n => "cp " ++ n.name

def printSign : Sign → String
  | .plus => "+"
  | .tilde => "~"
  | .quest => "?"

def printArgList (args : List Arg) : String :=
  if args.isEmpty then ""
  else
    let xs := args.map fun a => printSign a.sign ++ tokIdent a.param.name
    "[" ++ ", ".intercalate xs ++ "]"

def printGSym : Sym → String
  | .t t => printTerminal t
  | .nt n args => "|" ++ tokIdent n.name ++ printArgList args ++ "|"

def printLookItem : LookItem → String
  | .t t => printTerminal t
  | .noLT => "noLT"

def printLookSeq (xs : List LookItem) : String :=
  " ".intercalate (xs.map printLookItem)

def printGItem : Item → String
  | .sym s opt => printGSym s ++ (if opt then "?" else "")
  | .lookahead (.eq xs) => "[lookahead == " ++ printLookSeq xs ++ "]"
  | .lookahead (.ne xs) => "[lookahead != " ++ printLookSeq xs ++ "]"
  | .lookahead (.mem ss) => "[lookahead in { " ++ ", ".intercalate (ss.map printLookSeq) ++ " }]"
  | .lookahead (.notMem ss) => "[lookahead not_in { " ++ ", ".intercalate (ss.map printLookSeq) ++ " }]"
  | .lookahead (.notMemNT nt) => "[lookahead not_in |" ++ tokIdent nt.name ++ "|]"
  | .noLT => "[noLT]"
  | .empty => "[empty]"
  | .butNot s (.sym ex) => printGSym s ++ " butnot " ++ printGSym ex
  | .butNot s (.oneOf syms orSep) =>
    let sp := if orSep then "or" else "plain"
    printGSym s ++ " butnot one_of " ++ sp ++ " [" ++ ", ".intercalate (syms.map printGSym) ++ "]"
  | .onlyIf p => "[onlyIf " ++ Phrase.specName p ++ "]"
  | .phrase p => "> " ++ Phrase.specName p
where
  Phrase.specName : Phrase → String
    | .anyCodePoint => "anyCodePoint"
    | .idStart => "idStart"
    | .idContinue => "idContinue"
    | .leadSurrogate => "leadSurrogate"
    | .trailSurrogate => "trailSurrogate"
    | .mvAbove10FFFF => "mvAbove10FFFF"
    | .mvAtMost10FFFF => "mvAtMost10FFFF"
    | .mvLead => "mvLead"
    | .mvTrail => "mvTrail"
    | .mvNonSurrogate => "mvNonSurrogate"
    | .groupNumberAtMostCount => "groupNumberAtMostCount"

def printGuard (gs : List Guard) : String :=
  if gs.isEmpty then ""
  else
    let xs := gs.map fun g => (if g.plus then "+" else "~") ++ tokIdent g.param.name
    "[" ++ ", ".intercalate xs ++ "] "

def printAlt (a : Alt) : String :=
  let g := printGuard a.guard
  let rhs := " ".intercalate (a.rhs.map printGItem)
  let lbl := match a.label with | some l => " #label " ++ escStr l | none => ""
  "  | " ++ g ++ rhs ++ lbl ++ "\n"

def printRule (g : GrammarId) (r : Rule) : String :=
  let ps := ", ".intercalate (r.params.map fun p => tokIdent p.name)
  let hd := "rule " ++ grammarName g ++ " |" ++ tokIdent r.lhs.name ++ "| [" ++ ps ++ "] " ++ r.colons.print ++ " "
  let body := match r.body with
    | .alts alts => "{\n" ++ String.join (alts.map printAlt) ++ "}\n\n"
    | .oneOf rows =>
      "one_of {\n" ++
      String.join (rows.map fun row => "  row [" ++ ", ".intercalate (row.map printTerminal) ++ "]\n") ++
      "}\n\n"
  hd ++ body

def printGrammarFile (g : GrammarId) (rules : List Rule) : String :=
  "grammar " ++ grammarName g ++ "\n\n" ++ String.join (rules.map (printRule g))

def annexBName : AnnexB → String
  | .htmlLikeComments => "htmlLikeComments"
  | .regExpPatterns => "regExpPatterns"
  | .functionDeclarationsInIfStatement => "functionDeclarationsInIfStatement"
  | .initializersInForIn => "initializersInForIn"

def overlayModeName : OverlayMode → String
  | .extend => "extend"
  | .replace => "replace"

def overlayCondName : OverlayCond → String
  | .always => "always"
  | .notModule => "notModule"
  | .nonStrict => "nonStrict"

def printBlock (b : Block) : String :=
  let k := match b.kind with
    | .main => "main"
    | .supplemental n => "supplemental |" ++ tokIdent n.name ++ "|"
    | .overlay s m c => "overlay " ++ annexBName s ++ " " ++ overlayModeName m ++ " " ++ overlayCondName c
  let rs := ", ".intercalate (b.rules.map fun r => "|" ++ tokIdent r.lhs.name ++ "|")
  "block " ++ grammarName b.grammar ++ " " ++ tokClause b.clause ++ " " ++ k ++ " [" ++ rs ++ "]\n"

def goalSrcName : GoalSrc → String
  | .grammar => "grammar"
  | .parseText => "parseText"
  | .grammarSymbol => "grammarSymbol"
  | .syntaxOf => "syntaxOf"
  | .mustCover => "mustCover"
  | .supplemental => "supplemental"
  | .copy => "copy"
  | .json => "json"

def printGoal (g : Goal) : String :=
  "goal |" ++ tokIdent g.nt.name ++ "| " ++ printArgList g.args ++ " src " ++ goalSrcName g.src ++ "\n"

def syntacticProdKey (d : Decls) (byId : Array (Option Ecma.Grammar.Prod)) (p : Gen.Syntactic.Production) : String :=
  let pid := (byId.findIdx? fun o => o.any fun pr =>
    pr.grammar == .syntactic && pr.ctor == p.ctorIdx && pr.mask.all (!·)).getD 0
  d.prods.getD pid ""

def printCover (d : Decls) (byId : Array (Option Ecma.Grammar.Prod)) (cv : Cover Gen.Syntactic.Production) : String :=
  let ctx := syntacticProdKey d byId cv.context
  "cover " ++ tokProd ctx ++ " cover |" ++ tokIdent cv.cover.name ++ "| refined |" ++ tokIdent cv.refined.name ++ "|\n"

def semiName : Semi → String
  | .insertable => "insertable"
  | .doWhile => "doWhile"
  | .emptyStatement => "emptyStatement"
  | .forHeader => "forHeader"
  | .forHeaderIfDeclaration => "forHeaderIfDeclaration"

def printSemi (d : Decls) (byId : Array (Option Ecma.Grammar.Prod)) (s : SemiSite Gen.Syntactic.Production) : String :=
  let pk := syntacticProdKey d byId s.prod
  "semi " ++ tokProd pk ++ " pos " ++ toString s.pos ++ " " ++ semiName s.semi ++ "\n"

def printGrammarIndex (d : Decls) : String :=
  let byId := prodsById Gen.grammars Gen.prodIds Gen.prodNext
  "-- Grammar parameters, nonterminals, blocks, goals, covers, and ASI semicolons\n\n" ++
  String.join (d.params.toList.map fun p => "param " ++ tokIdent p ++ "\n") ++ "\n" ++
  String.join (d.nts.toList.map fun n => "nt " ++ tokIdent n ++ "\n") ++ "\n" ++
  String.join (Gen.blocks.map printBlock) ++ "\n" ++
  String.join (Gen.goals.map printGoal) ++ "\n" ++
  String.join (Gen.covers.map (printCover d byId)) ++ "\n" ++
  String.join (Gen.semis.map (printSemi d byId))

end Ecma.Grammar.PrintSpecTec
