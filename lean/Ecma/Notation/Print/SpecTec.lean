module

public import Ecma.Notation.Syntax
public import Ecma.Notation.Early
public import Ecma.Notation.Tables
public import Ecma.Notation.Realm
public import Ecma.Grammar.PrintSpecTec

/-!
# Canonical SpecTec printers for declarations, clauses, early errors, tables, and realm

Byte-for-byte structurally recursive printers matching `crates/spectec/src/print.rs`
for `00-decls.spectec`, `08-early-errors.spectec`, `09-tables.spectec`,
`10-realm.spectec`, and `clauses/*.spectec`.
-/

@[expose] public section

namespace Ecma.Print.SpecTec

open Ecma Ecma.SpecTec

structure Env where
  d : Decls
  tblNames : Array String

def boolStr (b : Bool) : String := if b then "true" else "false"

def printSign : Sign → String
  | .none => ""
  | .plus => "+"
  | .minus => "-"

def printNumeral : Numeral → String
  | .dec v => toString v
  | .hex v d => s!"hex({v}, {escStr d})"
  | .frac w f p => s!"frac({w}, {f}, {p})"

def printMag : Mag → String
  | .num n => printNumeral n
  | .inf => "∞"

def printSub : Sub → String
  | .none => "n"
  | .f => "f"
  | .z => "z"

def printVal (e : Env) : ValLit → String
  | .undefined => "undefined"
  | .null => "null"
  | .true => "true"
  | .false => "false"
  | .this => "this"
  | .str s => escStr s
  | .nan sb => match sb with | .none => "nan" | .f => "nan_f" | .z => "nan_z"
  | .num sg m sb => s!"num_{printSub sb}({printSign sg}{printMag m})"
  | .err f => "err " ++ tokField (nameAt e.d.fields f)
  | .bigN n => s!"bign({printNumeral n})"

def exprPrec : Expr → Nat
  | .bin .add _ _ | .bin .sub _ _ | .bin .plus _ _ => 1
  | .bin .mul _ _ | .bin .div _ _ | .bin .modulo _ _ | .bin .times _ _ => 2
  | .bin .pow _ _ => 3
  | .un .. | .q _ | .bang _ => 4
  | _ => 5

def wrapPrec (minPrec : Nat) (child : Expr) (s : String) : String :=
  if exprPrec child < minPrec then "{" ++ s ++ "}" else s

def binSym : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .plus => "plus"
  | .mul => "*"
  | .div => "/"
  | .modulo => "modulo"
  | .times => "times"
  | .pow => "^"

def relSym : RelOp → String
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .eq => "=="
  | .ne => "!="

def conjStr : Conj → String
  | .and => "and"
  | .or => "or"

def printParamArgs (e : Env) : List (ParamId × Bool) → String
  | [] => ""
  | args =>
    let xs := args.map fun (p, b) => (if b then "+" else "~") ++ tokIdent (nameAt e.d.params p)
    "[" ++ ", ".intercalate xs ++ "]"

mutual

def printExpr (e : Env) (vs : Array String) : Expr → String
  | .var x => tokIdent (nameAt vs x)
  | .bnd x => "?" ++ tokIdent (nameAt vs x)
  | .val v => printVal e v
  | .math .none (.num (.dec n)) => toString n
  | .math sg m => s!"math({printSign sg}{printMag m})"
  | .enum en => tokEnum (nameAt e.d.enums en)
  | .param p => "param " ++ tokIdent (nameAt e.d.params p)
  | .intrinsic f => "intrinsic " ++ tokField (nameAt e.d.fields f)
  | .fieldName f => tokField (nameAt e.d.fields f)
  | .nt n args => "|" ++ tokIdent (nameAt e.d.nts n) ++ printParamArgs e args ++ "|"
  | .prod ps => "prods [" ++ ", ".intercalate (ps.map fun p => tokProd (nameAt e.d.prods p)) ++ "]"
  | .codeUnit n d nm =>
    let ns := match nm with | none => "none" | some s => escStr s
    s!"cu({n}, {escStr d}, {ns})"
  | .codePoint n d nm =>
    let ns := match nm with | none => "none" | some s => escStr s
    s!"cp({n}, {escStr d}, {ns})"
  | .code s => "code " ++ escStr s
  | .term s => "term " ++ escStr s
  | .call (.alg a) args => s!"{tokAlgRef e.d a}({", ".intercalate (printExprs e vs args)})"
  | .call (.prim p) args => s!"{tokPrim (nameAt e.d.prims p)}({", ".intercalate (printExprs e vs args)})"
  | .callAt a args => s!"call_at {tokAlgRef e.d a}({", ".intercalate (printExprs e vs args)})"
  | .sdo s sub args =>
    let ar := if args.isEmpty then "" else "; " ++ ", ".intercalate (printExprs e vs args)
    s!"sdo {tokIdent (nameAt e.d.sdos s)}({printExpr e vs sub}{ar})"
  | .component c sub =>
    s!"component {tokField (nameAt e.d.fields c)} of {wrapPrec 4 sub (printExpr e vs sub)}"
  | .field obj f =>
    wrapPrec 5 obj (printExpr e vs obj) ++ tokField (nameAt e.d.fields f)
  | .imethod obj m args =>
    s!"{wrapPrec 5 obj (printExpr e vs obj)}{tokField (nameAt e.d.fields m)}({", ".intercalate (printExprs e vs args)})"
  | .cmethod obj m args =>
    s!"{wrapPrec 5 obj (printExpr e vs obj)}.{tokIdent (nameAt e.d.methods m)}({", ".intercalate (printExprs e vs args)})"
  | .apply f args =>
    s!"{wrapPrec 5 f (printExpr e vs f)}({", ".intercalate (printExprs e vs args)})"
  | .index obj i => s!"{wrapPrec 5 obj (printExpr e vs obj)}[{printExpr e vs i}]"
  | .q x => "? " ++ wrapPrec 4 x (printExpr e vs x)
  | .bang x => "! " ++ wrapPrec 4 x (printExpr e vs x)
  | .un .neg x => "neg " ++ wrapPrec 4 x (printExpr e vs x)
  | .un .not x => "not " ++ wrapPrec 4 x (printExpr e vs x)
  | .bin op a b =>
    let p := match op with
      | .add | .sub | .plus => 1
      | .mul | .div | .modulo | .times => 2
      | .pow => 3
    let lp := if op == .pow then p + 1 else p
    let rp := if op == .pow then p else p + 1
    s!"{wrapPrec lp a (printExpr e vs a)} {binSym op} {wrapPrec rp b (printExpr e vs b)}"
  | .paren x => "(" ++ printExpr e vs x ++ ")"
  | .list es => "[" ++ ", ".intercalate (printExprs e vs es) ++ "]"
  | .record sort fs =>
    let ks := match sort with | none => "" | some s => " " ++ tokIdent (nameAt e.d.sorts s)
    if fs.isEmpty then s!"record{ks} " ++ "{}"
    else s!"record{ks} " ++ "{ " ++ ", ".intercalate (printFieldExprs e vs fs) ++ " }"
  | .resumedWith x => s!"resumed_with({printExpr e vs x})"
  | .thisNode => "this_node"
  | .child k n => s!"child {k} |{tokIdent (nameAt e.d.nts n)}|"
  | .childOf x n => s!"child_of({printExpr e vs x}, |{tokIdent (nameAt e.d.nts n)}|)"
  | .thisValue => "this_value"
  | .newTarget => "new_target"
  | .xref c => "clause " ++ tokClause (nameAt e.d.clauses c)
  | .closure site => "closure " ++ toString site
  | .table t => "table " ++ tokTable (nameAt e.tblNames t)
  | .definition c => "ref " ++ tokClause (nameAt e.d.clauses c)
  | .tableStep t k => s!"table_step({tokTable (nameAt e.tblNames t)}, {printExpr e vs k})"
  | .data (.sort s) => "data sort " ++ tokIdent (nameAt e.d.sorts s)
  | .data (.choice i) => "data choice " ++ toString i
  | .data .absent => "data absent"
  | .ofCond c => s!"bool({printCond e vs c})"

def printExprs (e : Env) (vs : Array String) : List Expr → List String
  | [] => []
  | x :: xs => printExpr e vs x :: printExprs e vs xs

def printFieldExprs (e : Env) (vs : Array String) : List (FieldId × Expr) → List String
  | [] => []
  | (f, v) :: fs => (tokField (nameAt e.d.fields f) ++ ": " ++ printExpr e vs v) :: printFieldExprs e vs fs

def printPred (e : Env) (vs : Array String) : Pred → String
  | .isVal neg nei vals =>
    let n := if neg then " not" else ""
    let neiS := if nei then " neither" else ""
    s!"is{n}{neiS} val " ++ "{" ++ "; ".intercalate (printExprs e vs vals) ++ "}"
  | .isTy neg nei tys =>
    let n := if neg then " not" else ""
    let neiS := if nei then " neither" else ""
    s!"is{n}{neiS} ty " ++ "{" ++ "; ".intercalate (printTys e vs tys) ++ "}"
  | .call (.alg a) args neg =>
    s!"{if neg then "fails" else "sat"} {tokAlgRef e.d a}({", ".intercalate (printExprs e vs args)})"
  | .call (.prim p) args neg =>
    s!"{if neg then "fails" else "sat"} {tokPrim (nameAt e.d.prims p)}({", ".intercalate (printExprs e vs args)})"

def printConjPreds (e : Env) (vs : Array String) : List (Conj × Pred) → String
  | [] => ""
  | (j, pr) :: rest => " " ++ conjStr j ++ " " ++ printPred e vs pr ++ printConjPreds e vs rest

def printCond (e : Env) (vs : Array String) : Cond → String
  | .preds ex p rest => printExpr e vs ex ++ " " ++ printPred e vs p ++ printConjPreds e vs rest
  | .rel op a b => s!"{printExpr e vs a} {relSym op} {printExpr e vs b}"
  | .and [] => "all []"
  | .and cs => " and ".intercalate (printAndKids e vs cs)
  | .or [] => "any []"
  | .or cs => " or ".intercalate (printOrKids e vs cs)
  | .paren c => "(" ++ printCond e vs c ++ ")"
  | .alg a => "alg " ++ tokAlgRef e.d a
  | .expr ex => "expr " ++ printExpr e vs ex
  | .pass k => "pass " ++ escStr k

def printAndKids (e : Env) (vs : Array String) : List Cond → List String
  | [] => []
  | c :: cs =>
    let wrap := match c with | .and _ | .or _ => true | _ => false
    let s := printCond e vs c
    (if wrap then "{" ++ s ++ "}" else s) :: printAndKids e vs cs

def printOrKids (e : Env) (vs : Array String) : List Cond → List String
  | [] => []
  | c :: cs =>
    let wrap := match c with | .or _ => true | _ => false
    let s := printCond e vs c
    (if wrap then "{" ++ s ++ "}" else s) :: printOrKids e vs cs

def printTy (e : Env) (vs : Array String) : TyExpr → String
  | .union ts => " | ".intercalate (printUnionKids e vs ts)
  | .sort [] s => tokIdent (nameAt e.d.sorts s)
  | .sort ms s =>
    let mstr := ", ".intercalate (ms.map fun m => tokIdent (nameAt e.d.sorts m))
    s!"sort [{mstr}] {tokIdent (nameAt e.d.sorts s)}"
  | .listOf inner => s!"list<{printTy e vs inner}>"
  | .seqOf inner => s!"seq<{printTy e vs inner}>"
  | .butNot a b => s!"butnot({printTy e vs a}, {printTy e vs b})"
  | .doc s => "doc " ++ escStr s
  | .completion none => "completion<none>"
  | .completion (some inner) => s!"completion<{printTy e vs inner}>"
  | .interval base lo hi =>
    let wrap := match base with | .union _ => true | _ => false
    let b := printTy e vs base
    let bs := if wrap then "{" ++ b ++ "}" else b
    s!"interval {bs} [{printExpr e vs lo}, {printExpr e vs hi}]"
  | .value ex => s!"val({printExpr e vs ex})"
  | .var x => "var " ++ tokIdent (nameAt vs x)
  | .nt n => "|" ++ tokIdent (nameAt e.d.nts n) ++ "|"
  | .record [] => "record {}"
  | .record fs => "record { " ++ ", ".intercalate (printFieldTys e vs fs) ++ " }"
  | .that base p rest =>
    let wrap := match base with | .union _ | .that .. => true | _ => false
    let b := printTy e vs base
    let bs := if wrap then "{" ++ b ++ "}" else b
    bs ++ " that " ++ printPred e vs p ++ printConjPreds e vs rest
  | .pred p => s!"pred({printPred e vs p})"

def printUnionKids (e : Env) (vs : Array String) : List TyExpr → List String
  | [] => []
  | t :: ts =>
    let wrap := match t with | .union _ => true | _ => false
    let s := printTy e vs t
    (if wrap then "{" ++ s ++ "}" else s) :: printUnionKids e vs ts

def printTys (e : Env) (vs : Array String) : List TyExpr → List String
  | [] => []
  | t :: ts => printTy e vs t :: printTys e vs ts

def printFieldTys (e : Env) (vs : Array String) : List (FieldId × TyExpr) → List String
  | [] => []
  | (f, t) :: fs => (tokField (nameAt e.d.fields f) ++ ": " ++ printTy e vs t) :: printFieldTys e vs fs

end

mutual

def printBody (e : Env) (vs : Array String) (ind : Nat) : Body → String
  | .inline s => "-> " ++ printStmt e vs ind s
  | .block ns => "{\n" ++ printStmts e vs (ind + 2) ns ++ spaces ind ++ "}"

def printArm (e : Env) (vs : Array String) (ind : Nat) : Arm → String
  | .mk (some c) bd => spaces ind ++ "else_if " ++ printCond e vs c ++ " " ++ printBody e vs ind bd
  | .mk none bd => spaces ind ++ "else " ++ printBody e vs ind bd

def printArms (e : Env) (vs : Array String) (ind : Nat) : List Arm → String
  | [] => ""
  | a :: as => "\n" ++ printArm e vs ind a ++ printArms e vs ind as

def printOptArm (e : Env) (vs : Array String) (ind : Nat) : Option Arm → String
  | none => ""
  | some a => "\n" ++ printArm e vs ind a

def printStmt (e : Env) (vs : Array String) (ind : Nat) : Stmt → String
  | .let_ x ex => s!"let {tokIdent (nameAt vs x)} = {printExpr e vs ex}"
  | .set (.var x) ex => s!"set var {tokIdent (nameAt vs x)} = {printExpr e vs ex}"
  | .set (.field o f) ex =>
    s!"set field {wrapPrec 5 o (printExpr e vs o)}{tokField (nameAt e.d.fields f)} = {printExpr e vs ex}"
  | .set (.expr lhs) ex => s!"set expr {wrapPrec 5 lhs (printExpr e vs lhs)} = {printExpr e vs ex}"
  | .ret none => "return"
  | .ret (some ex) => "return " ++ printExpr e vs ex
  | .perform ex => "perform " ++ printExpr e vs ex
  | .if_ c bd arms els =>
    "if " ++ printCond e vs c ++ " " ++ printBody e vs ind bd ++ printArms e vs ind arms ++ printOptArm e vs ind els
  | .ifElse c s1 s2 =>
    s!"if_else {printCond e vs c} " ++ "{ " ++ printStmt e vs ind s1 ++ " } else { " ++ printStmt e vs ind s2 ++ " }"
  | .assert c => "assert " ++ printCond e vs c
  | .assertAlways c => "assert! " ++ printCond e vs c
  | .assertIf c l => s!"assert_if {printCond e vs c} then {printCond e vs l}"
  | .unreachable v => s!"unreachable {v}"
  | .throwVal ex => "throw " ++ printExpr e vs ex
  | .note s => "note " ++ escStr s
  | .repeat_ ns => "repeat {\n" ++ printStmts e vs (ind + 2) ns ++ spaces ind ++ "}"
  | .repeatWhile c ns => "repeat_while " ++ printCond e vs c ++ " {\n" ++ printStmts e vs (ind + 2) ns ++ spaces ind ++ "}"
  | .repeatUntil c ns => "repeat_until " ++ printCond e vs c ++ " {\n" ++ printStmts e vs (ind + 2) ns ++ spaces ind ++ "}"
  | .forEach x tyOpt list rev bd =>
    let ts := match tyOpt with | none => "" | some t => " : " ++ printTy e vs t
    let rs := if rev then " rev" else ""
    s!"for_each {tokIdent (nameAt vs x)}{ts}{rs} in {printExpr e vs list} {printBody e vs ind bd}"
  | .forEachRec fs x list bd =>
    let fss := ", ".intercalate (fs.map fun f => tokField (nameAt e.d.fields f))
    s!"for_each_rec [{fss}] {tokIdent (nameAt vs x)} in {printExpr e vs list} {printBody e vs ind bd}"
  | .forRange x lo li hi hi' desc bd =>
    let lk := if li then "incl" else "excl"
    let hk := if hi' then "incl" else "excl"
    let dk := if desc then " desc" else ""
    s!"for_range {tokIdent (nameAt vs x)} {lk} {printExpr e vs lo} .. {hk} {printExpr e vs hi}{dk} {printBody e vs ind bd}"
  | .forKeys x obj c ord bd =>
    s!"for_keys {tokIdent (nameAt vs x)} of {printExpr e vs obj} where {printCond e vs c} order {ord} {printBody e vs ind bd}"
  | .forIndex x list bd =>
    s!"for_index {tokIdent (nameAt vs x)} of {printExpr e vs list} {printBody e vs ind bd}"
  | .forChildren x bd => s!"for_children {tokIdent (nameAt vs x)} {printBody e vs ind bd}"
  | .forChildrenOf x ex bd =>
    s!"for_children_of {tokIdent (nameAt vs x)} in {printExpr e vs ex} {printBody e vs ind bd}"
  | .repeatN ex ns => "repeat_n " ++ printExpr e vs ex ++ " {\n" ++ printStmts e vs (ind + 2) ns ++ spaces ind ++ "}"
  | .suspend ex v => s!"suspend {printExpr e vs ex} kind {v}"
  | .push ex v => s!"push {printExpr e vs ex} kind {v}"
  | .remove ex v => s!"remove {printExpr e vs ex} kind {v}"
  | .removeRestore ex r => s!"remove_restore {printExpr e vs ex} with {printExpr e vs r}"
  | .resumeTop => "resume_top"
  | .resumeLet ctx val x => s!"resume_let {printExpr e vs ctx} with {printExpr e vs val} -> {tokIdent (nameAt vs x)}"
  | .resume ex v => s!"resume {printExpr e vs ex} with {printExpr e vs v}"
  | .setCodeState ex f => s!"set_code_state {printExpr e vs ex} to {printExpr e vs f}"
  | .block ns => "block {\n" ++ printStmts e vs (ind + 2) ns ++ spaces ind ++ "}"

def printStmts (e : Env) (vs : Array String) (ind : Nat) : List Stmt → String
  | [] => ""
  | s :: ns => spaces ind ++ printStmt e vs ind s ++ "\n" ++ printStmts e vs ind ns

end

def algKindStr : AlgKind → String
  | .ao => "ao"
  | .sdo => "sdo"
  | .builtin => "builtin"
  | .internalMethod => "internal_method"
  | .concreteMethod => "concrete_method"
  | .numericMethod => "numeric_method"
  | .hostDefined => "host_defined"
  | .implDefined => "impl_defined"
  | .untyped => "untyped"

def cloKindStr : CloKind → String
  | .abstract => "abstract"
  | .job => "job"
  | .matcher => "matcher"
  | .matcherContinuation => "matcher_continuation"
  | .readModifyWrite => "read_modify_write"

def printHeader (e : Env) (vs : Array String) (h : Header) : String :=
  let r := match h.recv with
    | none => ""
    | some (x, t) => s!" recv {tokIdent (nameAt vs x)} : {printTy e vs t}"
  let ps := h.params.map fun p =>
    let t := match p.ty with | none => "" | some ty => " : " ++ printTy e vs ty
    let o := if p.optional then " opt" else ""
    let rs := if p.rest then " rest" else ""
    s!"{tokIdent (nameAt vs p.x)}{t}{o}{rs}"
  let ret := match h.ret with | none => "" | some t => " -> " ++ printTy e vs t
  s!"kind {algKindStr h.kind}{r} params [{", ".intercalate ps}]{ret}"

def printSdoHeader (e : Env) (h : Header) : String :=
  let sdoVars := #["v0", "v1", "v2", "v3"]
  let r := match h.recv with
    | none => ""
    | some (s, t) => s!" recv slot {s} : {printTy e sdoVars t}"
  let ps := h.params.map fun p =>
    let t := match p.ty with | none => "" | some ty => " : " ++ printTy e sdoVars ty
    let o := if p.optional then " opt" else ""
    let rs := if p.rest then " rest" else ""
    s!"slot {p.x}{t}{o}{rs}"
  let ret := match h.ret with | none => "" | some t => " -> " ++ printTy e sdoVars t
  s!"kind {algKindStr h.kind}{r} params [{", ".intercalate ps}]{ret}"

def printClosure (e : Env) (vs : Array String) (ind : Nat) (c : CloLit) : String :=
  let pStr := match c.params with
    | none => "none"
    | some ps => "[" ++ ", ".intercalate (ps.map fun p => tokIdent (nameAt vs p)) ++ "]"
  let cStr := ", ".intercalate (c.caps.map fun p => tokIdent (nameAt vs p))
  let fStr := match c.frame with
    | none => ""
    | some (a, b, d) => s!" frame ({tokIdent (nameAt vs a)}, {tokIdent (nameAt vs b)}, {tokIdent (nameAt vs d)})"
  let atom := if c.atomic then " atomic" else ""
  spaces ind ++ s!"closure {cloKindStr c.kind}{atom} params {pStr} captures [{cStr}]{fStr} " ++ "{\n" ++
  printStmts e vs (ind + 2) c.body ++ spaces ind ++ "}\n"

def printAlg (e : Env) (a : Alg) : String :=
  let vs := ", ".intercalate (a.vars.toList.map tokIdent)
  s!"def {tokAlgRef e.d a.id} {escStr a.name} ({printHeader e a.vars a.header}) vars [{vs}] " ++ "{\n" ++
  printStmts e a.vars 2 a.body ++
  String.join (a.closures.toList.map (printClosure e a.vars 2)) ++
  "}\n\n"

def printSdoRow (e : Env) (r : SdoRow) : String :=
  let fstr := match r.form with | .alg => "alg" | .equation => "equation"
  let ann := if r.annex then " annex" else ""
  let ps := ", ".intercalate (r.prods.map fun p => tokProd (nameAt e.d.prods p))
  let ks := ", ".intercalate (r.keys.map escStr)
  let vs := ", ".intercalate (r.vars.toList.map tokIdent)
  s!"sdo_row {tokAlgRef e.d r.id} {tokIdent (nameAt e.d.sdos r.sdo)} form {fstr}{ann} " ++ "{\n" ++
  s!"  prods [{ps}]\n  keys [{ks}]\n  vars [{vs}]\n  steps " ++ "{\n" ++
  printStmts e r.vars 4 r.body ++ "  }\n" ++
  String.join (r.closures.toList.map (printClosure e r.vars 2)) ++
  "}\n\n"

def printChapterFile (e : Env) (stem : String) (algs : List Alg) (rows : List SdoRow) : String :=
  s!"-- ECMA-262 SpecTec Clauses: {stem}\n\n" ++
  String.join (algs.map (printAlg e)) ++
  String.join (rows.map (printSdoRow e))

def printEarlySentInner (e : Env) (vs : Array String) (ind : Nat) : EarlySentence → String
  | .syntaxError early cond unlessOpt =>
    let hd := if early then "early_syntax_error" else "syntax_error"
    let u := match unlessOpt with
      | none => ""
      | some (uf, cond2) =>
        let ufs := match uf with | .plain => "plain" | .comma => "comma" | .optional => "opt"
        s!" unless {ufs} {printCond e vs cond2}"
    s!"{hd} {printCond e vs cond}{u}"
  | .syntaxErrorIns a b => s!"syntax_error_ins {printCond e vs a} & {printCond e vs b}"
  | .mustCover ex ty => s!"must_cover {printExpr e vs ex} : {printTy e vs ty}"
  | .rulesApplied ps raw =>
    let ks := ", ".intercalate (ps.map fun p => tokProd (nameAt e.d.prods p))
    s!"rules_applied [{ks}] {escStr raw}"
  | .ifInline cond inner =>
    s!"if_inline {printCond e vs cond} -> {printEarlySentInner e vs 0 inner}"
  | .info st => "info { " ++ printStmt e vs ind st ++ " }"
  | .notApplied cond st => s!"not_applied {printCond e vs cond} " ++ "{ " ++ printStmt e vs ind st ++ " }"
  | .forEachIn x ty list cond st =>
    s!"for_each_in {tokIdent (nameAt vs x)} : {printTy e vs ty} in {printExpr e vs list} where {printCond e vs cond} " ++
    "{ " ++ printStmt e vs ind st ++ " }"
  | .stmt st => "stmt { " ++ printStmt e vs ind st ++ " }"

def printEarlyRow (e : Env) (r : EarlyRow) : String :=
  let ps := ", ".intercalate (r.prods.map fun p => tokProd (nameAt e.d.prods p))
  let ks := ", ".intercalate (r.keys.map escStr)
  let vs := ", ".intercalate (r.vars.toList.map tokIdent)
  let m := if r.modifies then " modifies" else ""
  s!"early {tokAlgRef e.d r.id} {tokIdent (nameAt e.d.sdos r.sdo)}{m} " ++ "{\n" ++
  s!"  prods [{ps}]\n  keys [{ks}]\n  vars [{vs}]\n  sentences " ++ "{\n" ++
  String.join (r.body.map fun s => spaces 4 ++ printEarlySentInner e r.vars 4 s ++ "\n") ++
  "  }\n}\n\n"

def printEarlyErrorsFile (e : Env) (rows : List EarlyRow) : String :=
  "-- ECMA-262 Static Semantics: Early Errors\n\n" ++
  String.join (rows.map (printEarlyRow e))

def printTTy (e : Env) (vs : Array String) : TTy → String
  | .ty t => printTy e vs t
  | .records fs =>
    let xs := fs.map fun (f, t) => s!"{tokField (nameAt e.d.fields f)}: {printTy e vs t}"
    "records [" ++ ", ".intercalate xs ++ "]"

def printSig (e : Env) (vs : Array String) (g : Sig) : String :=
  let hd := match g.name with
    | .internal f => "field " ++ tokField (nameAt e.d.fields f)
    | .method m => "method " ++ tokIdent (nameAt e.d.methods m)
  let ps := g.params.map fun p =>
    s!"{tokIdent (nameAt vs p.x)}: {printTTy e vs p.ty}{if p.optional then " opt" else ""}"
  s!"{hd} ({", ".intercalate ps}) -> {printTTy e vs g.ret}"

mutual

def printCellBody (e : Env) (vs : Array String) : CellBody → String
  | .field f => "field " ++ tokField (nameAt e.d.fields f)
  | .ty t => "ty (" ++ printTTy e vs t ++ ")"
  | .sig g => "sig (" ++ printSig e vs g ++ ")"
  | .stmt st => "stmt { " ++ printStmt e vs 0 st ++ " }"
  | .alg a => "alg " ++ tokAlgRef e.d a
  | .expr ex => "expr (" ++ printExpr e vs ex ++ ")"
  | .op c => "op " ++ tokClause (nameAt e.d.clauses c)
  | .component f => "component " ++ tokField (nameAt e.d.fields f)
  | .name s => "name " ++ escStr s
  | .lines cs => "lines [" ++ ", ".intercalate (printCellBodies e vs cs) ++ "]"
  | .dfn c => "dfn (" ++ printCellBody e vs c ++ ")"
  | .code c => "code (" ++ printCellBody e vs c ++ ")"
  | .link h c => s!"link {escStr h} ({printCellBody e vs c})"
  | .raw s => "raw " ++ escStr s
  | .text s => "text " ++ escStr s

def printCellBodies (e : Env) (vs : Array String) : List CellBody → List String
  | [] => []
  | c :: cs => printCellBody e vs c :: printCellBodies e vs cs

end

def tableKindStr : TableKind → String
  | .fields => "fields"
  | .slots => "slots"
  | .internalMethods => "internal_methods"
  | .abstractMethods => "abstract_methods"
  | .components => "components"
  | .properties => "properties"
  | .intrinsics => "intrinsics"
  | .conversion => "conversion"
  | .data => "data"

def printTable (e : Env) (tname : String) (t : Table) : String :=
  if t.rows.isEmpty && t.clause == 0 && !t.thead then
    s!"table {tokTable tname} retired\n\n"
  else
    let cap := match t.caption with | none => "" | some s => s!"  caption {escStr s}\n"
    let sch := match t.schema with | none => "" | some (s, hd) => s!"  schema ({escStr s}, {boolStr hd})\n"
    let vs := ", ".intercalate (t.vars.toList.map tokIdent)
    let rowsStr := String.join (t.rows.map fun r =>
      "    row [\n" ++
      String.join (r.cells.map fun c =>
        let sp := if c.rowspan == 1 && c.colspan == 1 then "" else s!" span ({c.rowspan}, {c.colspan})"
        s!"      cell{sp} " ++ "{ " ++ printCellBody e t.vars c.body ++ " }\n") ++
      "    ]\n")
    s!"table {tokTable tname} {tokClause (nameAt e.d.clauses t.clause)}#{t.idx} " ++ "{\n" ++
    s!"  kind {tableKindStr t.kind}\n  thead {boolStr t.thead}\n{cap}{sch}  vars [{vs}]\n  rows [\n" ++
    rowsStr ++ "  ]\n}\n\n"

def printTablesFile (e : Env) (names : List String) (tables : List Table) : String :=
  "-- ECMA-262 Tables\n\n" ++
  String.join ((names.zip tables).map fun (n, t) => printTable e n t)

def printRKey : RKey → String
  | .str s => "str " ++ escStr s
  | .sym s => "sym " ++ escStr s

def printRVal (e : Env) : RVal → String
  | .undefined => "undefined"
  | .null => "null"
  | .bool b => boolStr b
  | .str s => escStr s
  | .number bits => "number " ++ toString bits.toNat
  | .obj i => "obj " ++ toString i
  | .sym d => "sym " ++ escStr d
  | .globalThis => "global_this"
  | .created a => "created " ++ tokAlgRef e.d a

def printRAttrs (a : RAttrs) : String :=
  s!"\{ w: {boolStr a.writable}, e: {boolStr a.enumerable}, c: {boolStr a.configurable} }"

def printRProp (e : Env) (p : RProp) : String :=
  let vs := match p.val with
    | .data v => s!"data ({printRVal e v})"
    | .accessor g s =>
      let opt : Option Nat → String
        | none => "none"
        | some n => "some " ++ toString n
      s!"accessor ({opt g}, {opt s})"
  let flags := (if p.annexB then " annexB" else "") ++
    (if p.optional then " opt" else "") ++
    (if p.omittable then " omittable" else "")
  s!"      prop {printRKey p.key} = {vs} attrs {printRAttrs p.attrs} {tokClause (nameAt e.d.clauses p.clause)}{flags}\n"

def printRObj (e : Env) (idx : Nat) (o : RObj) : String :=
  let ns := ", ".intercalate (o.names.map fun f => tokField (nameAt e.d.fields f))
  let ks := ", ".intercalate (o.keys.map fun f => tokField (nameAt e.d.fields f))
  let kstr := match o.kind with
    | .ordinary => "ordinary"
    | .exotic c => "exotic " ++ tokClause (nameAt e.d.clauses c)
  let proto := match o.proto with | none => "none" | some p => "some " ++ toString p
  let slots := ", ".intercalate (o.slots.map fun (f, v) => s!"({tokField (nameAt e.d.fields f)}, {printRVal e v})")
  let fstr := match o.fn? with
    | none => ""
    | some f =>
      let astr := match f.alg with | none => "none" | some a => "some " ++ tokAlgRef e.d a
      let pstr := match f.pfx with | none => "none" | some p => "some " ++ escStr p
      s!"  fn \{ alg {astr} len {f.length} name {printRKey f.name} pfx {pstr} ctor {boolStr f.ctor} async {boolStr f.async} len_attrs {printRAttrs f.lengthAttrs} name_attrs {printRAttrs f.nameAttrs} }\n"
  let flags := (if o.annexB then " annexB" else "") ++ (if o.optional then " opt" else "")
  let propsStr := if o.props.isEmpty then "  props []\n}\n\n"
    else "  props [\n" ++ String.join (o.props.map (printRProp e)) ++ "  ]\n}\n\n"
  s!"obj {idx} {escStr o.path} {tokClause (nameAt e.d.clauses o.clause)}{flags} " ++ "{\n" ++
  s!"  names [{ns}]\n  keys [{ks}]\n  kind {kstr}\n  proto {proto} extensible {boolStr o.extensible}\n  slots [{slots}]\n{fstr}{propsStr}"

def printRealmFile (e : Env) (r : RealmTable) : String :=
  let syms := ", ".intercalate (r.symbols.map escStr)
  let objsStr := String.join (r.objs.zipIdx.map fun (o, i) => printRObj e i o)
  let cpsStr := String.join (r.clauseProps.map fun (c, ps) =>
    s!"clause_props {tokClause (nameAt e.d.clauses c)} [\n" ++
    String.join (ps.map (printRProp e)) ++ "]\n\n")
  "-- ECMA-262 Intrinsic Objects and Built-ins (Realm Table)\n\n" ++
  s!"symbols [{syms}]\n\n" ++ objsStr ++ cpsStr

def printSortTest (e : Env) : SortTest → String
  | .none => "none"
  | .alg a => "alg " ++ tokAlgRef e.d a
  | .prim p args neg =>
    let as_ := args.map fun
      | .subject => "subject"
      | .enum en => tokEnum (nameAt e.d.enums en)
    s!"{if neg then "not " else ""}{tokPrim (nameAt e.d.prims p)}({", ".intercalate as_})"

def printDeclsFile (e : Env) (sortAliases : Array (String × String)) : String :=
  let d := e.d
  let clausesStr := String.join (d.clauses.toList.zipIdx.map fun (c, i) =>
    let op := d.ops.getD i ""
    if op.isEmpty then s!"clause {tokClause c}\n" else s!"clause {tokClause c} op {escStr op}\n")
  let fieldsStr := String.join (d.fields.toList.map fun f => s!"field {tokField f}\n")
  let enumsStr := String.join (d.enums.toList.map fun en => s!"enum {tokEnum en}\n")
  let methodsStr := String.join (d.methods.toList.map fun m => s!"method {tokIdent m}\n")
  let primsStr := String.join (d.prims.toList.zipIdx.map fun (p, i) =>
    let doc := d.primDocs.getD i ⟨"", ""⟩
    if doc.sig.isEmpty && doc.meaning.isEmpty then s!"extern def {tokPrim p}\n"
    else s!"extern def {tokPrim p} " ++ "{ " ++ s!"sig {escStr doc.sig} meaning {escStr doc.meaning}" ++ " }\n")
  let sortsStr := String.join (d.sorts.toList.zipIdx.map fun (s, i) =>
    match d.sortDefs.getD i none with
    | none => s!"syntax {tokIdent s}\n"
    | some sd =>
      if sd.super.isEmpty && !sd.record && sd.test == .none then
        s!"syntax {tokIdent s} defined " ++ "{}\n"
      else
        let su := ", ".intercalate (sd.super.map fun id => tokIdent (nameAt d.sorts id))
        s!"syntax {tokIdent s} defined " ++ "{ " ++
        s!"super [{su}] record {boolStr sd.record} test {printSortTest e sd.test}" ++ " }\n")
  let sdosStr := String.join (d.sdos.toList.zipIdx.map fun (s, i) =>
    let hd := d.sdoHeaders.getD i none
    let df := d.sdoDefaults.getD i none
    if hd.isNone && df.isNone then s!"sdo {tokIdent s}\n"
    else
      let hStr := match hd with | none => "" | some h => s!" header ({printSdoHeader e h})"
      let dStr := match df with | none => "" | some a => s!" default {tokAlgRef d a}"
      s!"sdo {tokIdent s} " ++ "{" ++ hStr ++ dStr ++ " }\n")
  let jobsStr := "checked_jobs [" ++ ", ".intercalate (d.checkedJobs.toList.map fun c => tokClause (nameAt d.clauses c)) ++ "]\n"
  let aliasesStr := String.join (sortAliases.toList.map fun (fr, to_) => s!"sort_alias {escStr fr} -> {tokIdent to_}\n")
  let gAltsStr := String.join (d.alts.toList.map fun (n, ts) =>
    let xs := ts.map fun | .text x => escStr x | .cp c => "cp " ++ escStr c
    s!"grammar_alt |{tokIdent (nameAt d.nts n)}| = [{", ".intercalate xs}]\n")
  let cProdsStr := String.join (d.clauseProds.toList.map fun (c, ps) =>
    let xs := ps.map fun p => tokProd (nameAt d.prods p)
    s!"clause_prods {tokClause (nameAt d.clauses c)} = [{", ".intercalate xs}]\n")
  "-- ECMA-262 SpecTec Declarations (bootstrapped from Ecma.Spec.src)\n\n" ++
  clausesStr ++ "\n" ++ fieldsStr ++ "\n" ++ enumsStr ++ "\n" ++ methodsStr ++ "\n" ++
  primsStr ++ "\n" ++ sortsStr ++ "\n" ++ sdosStr ++ "\n" ++ jobsStr ++ "\n" ++
  aliasesStr ++ "\n" ++ gAltsStr ++ "\n" ++ cProdsStr

end Ecma.Print.SpecTec
