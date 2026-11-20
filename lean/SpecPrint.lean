import Ecma.Notation.Print.Early
import Ecma.Notation.Print.Tables
import Ecma.Notation.Print.Overlay
import Ecma.Grammar.Print
import Ecma.Gen.Decls
import Ecma.Gen.Index
import Ecma.Gen.Early
import Ecma.Gen.Tables
import Ecma.Grammar.Gen.Index
import Ecma.Grammar.Gen.Readings

/-!
# ecma-print: the specification's data, printed back as its text

Every algorithm, SDO row, early-error rule, table and grammar block of `Ecma.Gen` and
`Ecma.Grammar.Gen` as `Ecma.Print` and `Ecma.Grammar` print it, and what the data holds of the
overlay (spec/formal): the readings of steps, rules and grammar rules, the parameters of its
algorithms, its primitives, phrases, sorts and errata; and each SDO row's and early-error rule's
grammar keys, which the data holds verbatim. `scripts/bijection.py` compares every item with
spec.html and the overlay, each found there independently of the generators.

One item is a line `@@KIND WHERE`, its text, and a line `@@end`; an item with readings has, after
its own text, a line `@@alt READING` before each reading's text:

    @@alg CLAUSE IDX             an algorithm's emu-alg body (the text between its tags)
    @@row CLAUSE IDX             an SDO row's emu-alg body, or its equation bullet's content
    @@key CLAUSE IDX K           the Kth grammar key of an SDO row with an emu-alg, or of an early-error rule
    @@early CLAUSE IDX           an Early Errors bullet's content; a line `@@sdo NAME` before it
    @@table CLAUSE IDX           an emu-table element
    @@block CLAUSE LINE          a grammar definition block (the text between its tags)
    @@reading CLAUSE IDX ID      a step with readings: its line, then each reading's steps
    @@rule-reading CLAUSE IDX ID an early-error rule with readings: its sentences, then each reading's
    @@grammar-reading CLAUSE LINE RULE HASH ID   a grammar rule's reading: its definition block
    @@params CLAUSE              an overlay algorithm's parameters
    @@erratum ID NAME READING    an erratum, by its id: its name, the reading the model applies
    @@prim NAME                  a primitive's signature, then its meaning
    @@phrase N CAT               a phrase's template, then its meaning
    @@sort NAME                  a sort's declaration

Imports only `Ecma`: it builds without the engine.
-/

open Ecma

/-- One item: its head line, its text, the end line. -/
def item (out : IO.FS.Stream) (head text : String) : IO Unit :=
  out.putStr ("@@" ++ head ++ "\n" ++ text ++ "\n@@end\n")

/-- An item with readings: its own text, then each reading's. -/
def readings (out : IO.FS.Stream) (kind clause : String) (idx : Nat) (rs : List Print.Overlay.StepReading)
    (sep : String) : IO Unit :=
  for r in rs do
    item out s!"{kind} {clause} {idx} {Ecma.Gen.errataIds.getD r.erratum ""}"
      (r.line ++ String.join (r.alts.map fun (n, t) => "\n@@alt " ++ n ++ sep ++ t))

/-- A row's grammar keys, as the data holds them (the content of each `<emu-grammar>`). -/
def keys (out : IO.FS.Stream) (clause : String) (idx : Nat) (ks : List String) : IO Unit :=
  for (k, i) in ks.zipIdx do
    item out s!"key {clause} {idx} {i}" k

def main : IO Unit := do
  let out ← IO.getStdout
  let d := Ecma.Gen.decls
  let clause := fun (c : ClauseId) => d.clauses.getD c ""
  for m in Ecma.Gen.algs do
    for a in m do
      item out s!"alg {clause a.id.clause} {a.id.idx}" (Print.alg d a)
      readings out "reading" (clause a.id.clause) a.id.idx (Print.Overlay.stepReadings d a.vars a.closures a.body) ""
  for m in Ecma.Gen.rows do
    for r in m do
      item out s!"row {clause r.id.clause} {r.id.idx}" (Print.row d r)
      if let .alg _ := r.form then
        keys out (clause r.id.clause) r.id.idx r.keys
      readings out "reading" (clause r.id.clause) r.id.idx (Print.Overlay.rowReadings d r) ""
  for m in Ecma.Gen.earlyRows do
    for r in m do
      item out s!"early {clause r.id.clause} {r.id.idx}" ("@@sdo " ++ d.sdos.getD r.sdo "" ++ "\n" ++ Print.Early.row d r)
      if r.id.idx < 1000 then
        keys out (clause r.id.clause) r.id.idx r.keys
      readings out "rule-reading" (clause r.id.clause) r.id.idx (Print.Overlay.ruleReadings d r) "\n"
  let algs := Ecma.Gen.algs.flatten
  for m in Ecma.Gen.tables do
    for t in m do
      unless t.figure || t.rows.isEmpty do
        item out s!"table {clause t.clause} {t.idx}" (Print.Tables.table d algs t)
  for b in Ecma.Grammar.Gen.blocks do
    item out s!"block {b.clause} {b.line}" b.printExact
  for ((b, h), r) in (Ecma.Grammar.Gen.Reading.blocks.zip Ecma.Grammar.Gen.Reading.hashes).zip Ecma.Grammar.Gen.Reading.readings do
    let id := match r.erratum with
      | some e => Ecma.Gen.errataIds.getD e ""
      | none => "-"
    item out s!"grammar-reading {b.clause} {b.line} {r.rule.lhs.name} {h} {id}" b.printExact
  for a in Ecma.Gen.Phrases.algs do
    item out s!"params {clause a.id.clause}" (Print.Overlay.paramsText d a)
  for (n, doc) in d.prims.toList.zip d.primDocs.toList do
    unless doc.sig.isEmpty && doc.meaning.isEmpty do
      item out s!"prim {n}" (doc.sig ++ "\n" ++ doc.meaning)
  for (p, i) in d.phrases.toList.zipIdx do
    item out s!"phrase {i} {p.cat}" (Print.Overlay.templateText p.template ++ "\n" ++ Print.Overlay.meaningText d p.meaning)
  for (n, s) in d.sorts.toList.zip d.sortDefs.toList do
    if let some s := s then
      item out s!"sort {n}" (Print.Overlay.sortText d s)
  for ((n, id), r) in (d.errata.toList.zip Ecma.Gen.errataIds.toList).zip d.parity.toList do
    unless id.isEmpty do
      item out s!"erratum {id} {n} {Print.Overlay.readingName r}" ""
