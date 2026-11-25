import Ecma.Notation.Print.SpecTec
import Ecma.Gen.Decls
import Ecma.Gen.Index
import Ecma.Gen.Early
import Ecma.Gen.Tables
import Ecma.Gen.Realm

/-!
# `ecma-print`: print every SpecTec file back from the generated Lean data

Prints `@@file <rel_path>` .. `@@end` blocks for all 36 `.spectec` files in
`spec/spectec/`, purely from `Ecma.Gen.*` and `Ecma.Grammar.Gen.*`.
`scripts/bijection.py` compares each printed file with `spec/spectec/` byte
for byte.
-/

open Ecma Ecma.Print.SpecTec Ecma.Grammar.PrintSpecTec

private def emitFile (out : IO.FS.Stream) (rel text : String) : IO Unit := do
  out.putStrLn ("@@file " ++ rel)
  out.putStr text
  if !text.endsWith "\n" then out.putStr "\n"
  out.putStrLn "@@end"

def main : IO Unit := do
  let out ← IO.getStdout
  let env : Env := { d := Ecma.Gen.decls, tblNames := Ecma.Gen.tableNames }
  let realm : RealmTable := {
    objs := Ecma.Gen.Realm.objs
    clauseProps := Ecma.Gen.Realm.clauseProps
    symbols := Ecma.Gen.Realm.symbols
  }
  emitFile out "00-decls.spectec" (printDeclsFile env Ecma.Gen.sortAliases)
  emitFile out "01-grammar-numeric.spectec" (printGrammarFile .numericString Ecma.Grammar.Gen.NumericString.rules)
  emitFile out "02-grammar-lexical.spectec" (printGrammarFile .lexical Ecma.Grammar.Gen.Lexical.rules)
  emitFile out "03-grammar-syntactic.spectec" (printGrammarFile .syntactic Ecma.Grammar.Gen.Syntactic.rules)
  emitFile out "04-grammar-regexp.spectec" (printGrammarFile .regExp Ecma.Grammar.Gen.RegExp.rules)
  emitFile out "05-grammar-annexb.spectec" (printGrammarFile .annexB Ecma.Grammar.Gen.AnnexB.rules)
  emitFile out "06-grammar-json.spectec" (printGrammarFile .json Ecma.Grammar.Gen.JSON.rules)
  emitFile out "07-grammar-index.spectec" (printGrammarIndex env.d)
  emitFile out "08-early-errors.spectec" (printEarlyErrorsFile env Ecma.Gen.earlyRows.flatten)
  emitFile out "09-tables.spectec" (printTablesFile env Ecma.Gen.tableNames.toList Ecma.Gen.tables.flatten)
  emitFile out "10-realm.spectec" (printRealmFile env realm)
  for (stem, algs, rows) in Ecma.Gen.chapters do
    emitFile out ("clauses/" ++ stem ++ ".spectec") (printChapterFile env stem algs rows)
