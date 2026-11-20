module

public import Ecma.Notation.Syntax

/-!
# Ecma print: the data as spec.html's text

Each constructor prints as words and sub-terms (`P`), joined by the canonical
spacing rules (`join`); a step's nested steps, bullets and verbatim
continuation lines follow its line, laid out by depth. `alg` prints an algorithm's
`emu-alg` body and `row` an SDO row's; `ecma-print` prints every one of them and
`scripts/bijection.py` compares each with spec.html byte for byte.
-/

@[expose] public section

namespace Ecma.Print

open Ecma

/-- A printed part: text, and whether no space may precede it; `raw` is verbatim prose. -/
inductive P where
  | t (s : String) (glue : Bool)
  | raw (s : String) (glue : Bool)
  deriving Repr, BEq, Inhabited

/-- Parts that take no space before them. -/
def nospBefore : List String := [",", ".", ":", ";", ")", "]", "'s", "</sup>", "</sub>", "</emu-meta>", "</emu-not-ref>"]

/-- Parts that take no space after them. -/
def nospAfter : List String := ["(", "[", "<sup>", "<sub>", "<emu-not-ref>"]

/-- One part appended to the text so far (`s`, the previous part `prev`). -/
def joinStep : String × String → P → String × String
  | (s, prev), .t x g =>
    let sp := !s.isEmpty && !g && !nospBefore.contains x && !nospAfter.contains prev &&
      !prev.startsWith "<emu-meta" && !(x.startsWith "<sub>" && !x.startsWith "<sub>[")
    ((if sp then s ++ " " else s) ++ x, x)
  | (s, prev), .raw x g =>
    let sp := !s.isEmpty && !g && !nospAfter.contains prev && !prev.startsWith "<emu-meta"
    ((if sp then s ++ " " else s) ++ x, x)

/-- The parts joined by the canonical spacing rules. -/
def join (ps : List P) : String := (ps.foldl joinStep ("", "")).1

/-- Printed parts and the lines that follow the step (each starting with a newline). -/
abbrev Out := List P × String

/-- What printing needs: the tables, the variables, the closure literals (and their bodies,
printed from column 0), and the depth of the current step. Lines are printed from column 0
and indented where they are placed (`indentBy`). -/
structure Ctx where
  d : Decls
  vars : Array String
  cl : Array CloLit
  clos : Array String
  depth : Nat

/-- The context of a step's nested steps. -/
def Ctx.deeper (c : Ctx) : Ctx := { c with depth := c.depth + 1 }

def cat (os : List Out) : Out := (os.foldr (fun o acc => o.1 ++ acc) [], os.foldr (fun o acc => o.2 ++ acc) "")

/-- Glue on the first part. -/
def glue : Out → Out
  | (.t s _ :: r, a) => (.t s true :: r, a)
  | (.raw s _ :: r, a) => (.raw s true :: r, a)
  | o => o

def w (s : String) : Out := ([.t s false], "")

def gw (s : String) : Out := ([.t s true], "")

def words (s : String) : Out := cat ((s.splitOn " ").map w)

def after (s : String) : Out := ([], s)

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- Every line of `s` (each after a newline) indented by `k` more columns. -/
def indentBy (k : Nat) (s : String) : String := ("\n" ++ spaces k).intercalate (s.splitOn "\n")

/-- `xs` separated by `sep`. -/
def sepBy (sep : String) : List Out → List Out
  | [] => []
  | [x] => [x]
  | x :: r => x :: w sep :: sepBy sep r

/-- An English list: `a`, `a or b`, `a, b, or c`. -/
def english (conj : String) (xs : List Out) : Out :=
  let n := xs.length
  cat ((xs.zipIdx).map fun (x, i) =>
    if i == 0 then x
    else cat [if n > 2 then w "," else ([], ""), if i == n - 1 then w conj else ([], ""), x])

def name (a : Array String) (i : Nat) : String := a.getD i ""

/-- A variable's printed form: a call frame slot (`#` then words) prints as its words. -/
def varText (c : Ctx) (x : Slot) : String :=
  let n := name c.vars x
  if n.startsWith "#" then (n.drop 1).toString else "_" ++ n ++ "_"

/-- Whether `x that p r` is a context sort's refinement by its context phrase, which prints as `x`. -/
def isContext (c : Ctx) : TyExpr → Pred → List (Conj × Pred) → Bool
  | .sort _ _ s _, .phrase q _, [] => ((c.d.sortDefs[s]?).join.bind (·.context)) == some q
  | _, _, _ => false

def var (c : Ctx) (x : Slot) : Out :=
  let n := name c.vars x
  if n.startsWith "#" then words (n.drop 1).toString else w ("_" ++ n ++ "_")

def numeral : Numeral → String
  | .dec n => toString n
  | .hex _ d => "0x" ++ d
  | .frac n f k => toString n ++ "." ++ String.ofList (List.replicate (k - (toString f).length) '0') ++ toString f

def mag : Mag → String
  | .num n => numeral n
  | .inf => "∞"

def sign : Sign → String
  | .none => ""
  | .plus => "+"
  | .minus => "-"

def sub : Sub → String
  | .none => ""
  | .f => "<sub>𝔽</sub>"
  | .z => "<sub>ℤ</sub>"

/-- A literal as written: its text with `&` and `<` re-escaped, or the written form it keeps. -/
def written (s wr : String) : String :=
  if wr.isEmpty then (s.replace "&" "&amp;").replace "<" "&lt;" else wr

def val (c : Ctx) : ValLit → String
  | .undefined => "*undefined*"
  | .null => "*null*"
  | .true => "*true*"
  | .false => "*false*"
  | .this => "*this*"
  | .str s wr => "*\"" ++ written s wr ++ "\"*"
  | .nan s => "*NaN*" ++ sub s
  | .num sg m s => "*" ++ sign sg ++ mag m ++ "*" ++ sub s
  | .err i => "*" ++ name c.d.fields i ++ "*"
  | .bigN n => "`" ++ numeral n ++ "n`"

def xref : Xref → String
  | ⟨h, .plain, _⟩ => "<emu-xref href=\"#" ++ h ++ "\"></emu-xref>"
  | ⟨h, .title, _⟩ => "<emu-xref href=\"#" ++ h ++ "\" title></emu-xref>"
  | ⟨h, .content t, _⟩ => "<emu-xref href=\"#" ++ h ++ "\">" ++ t ++ "</emu-xref>"

def attrText (a : Attr) : String :=
  a.key ++ match a.value with
    | some v => "=\"" ++ v ++ "\""
    | none => ""

def field (c : Ctx) (f : FieldId) : String := "[[" ++ name c.d.fields f ++ "]]"

/-- A grammar symbol's parameters as written: `[+P, ~Q]`, or nothing. -/
def goalText (c : Ctx) (as : List (ParamId × Bool)) : String :=
  if as.isEmpty then "" else
    "[" ++ ", ".intercalate (as.map fun (p, b) => (if b then "+" else "~") ++ name c.d.params p) ++ "]"

def article : Article → Out
  | .the => w "the"
  | .none => ([], "")

def isHead (neg : Bool) : AltForm → Out
  | .either => cat [w "is", if neg then w "not" else ([], ""), w "either"]
  | .oneOf => cat [w "is", if neg then w "not" else ([], ""), w "one", w "of"]
  | .neither => cat [w "is", if neg then w "not" else ([], ""), w "neither"]
  | .or => cat [w "is", if neg then w "not" else ([], "")]

def alts (f : AltForm) (xs : List Out) : Out :=
  match f, xs with
  | .neither, [a, b] => cat [a, w "nor", b]
  | _, _ => english "or" xs

def conjWord : Conj → String
  | .and => "and"
  | .or => "or"

def relWord : RelOp → String
  | .lt => "&lt;"
  | .le => "≤"
  | .gt => ">"
  | .ge => "≥"
  | .eq => "="
  | .ne => "≠"

def binWord : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "×"
  | .div => "/"
  | .modulo => "modulo"
  | .pow => "^"
  | .plus => "plus"
  | .times => "times"

def cloWords : CloKind → String
  | .abstract => "Abstract Closure"
  | .job => "Job Abstract Closure"
  | .matcher => "Matcher"
  | .matcherContinuation => "MatcherContinuation"
  | .readModifyWrite => "read-modify-write modification function"

/-- The article before an error constructor's name. -/
def errArticle (n : String) : String :=
  if n.startsWith "A" || n.startsWith "E" || n.startsWith "I" || n.startsWith "O" then "an" else "a"

/-- A step line's attribute list: `[id="x", legacy] `. -/
def attrs (as : List Attr) : String :=
  if as.isEmpty then "" else "[" ++ ", ".intercalate (as.map attrText) ++ "] "

/-- Steps' first part lower-cased (an inline statement). -/
def lowerFirst : Out → Out
  | (.t s g :: r, a) => (.t s.decapitalize g :: r, a)
  | o => o

/-- Without its final full stop (an inline statement before `; else`). -/
def dropStop (o : Out) : Out :=
  match o.1.reverse with
  | .t "." _ :: r => (r.reverse, o.2)
  | _ => o

/-- A printed hole of a phrase: its parts, and its rendering after the template
(nested steps, bullets, continuation lines); or a choice index. -/
inductive HO where
  | out (inline : Out) (trailing : String)
  | w (i : Nat)

/-- A step line: indentation, marker, attributes, text. -/
def line (c : Ctx) (as : List Attr) (o : Out) : String :=
  "\n" ++ spaces (2 * c.depth) ++ "1. " ++ attrs as ++ join o.1 ++ o.2

mutual

/-- A phrase template filled with holes, from the pending glue flag `g`; the holes left over. -/
def fill (g : Bool) : List Piece → List HO → Out × List HO × Bool
  | [], hs => (([], ""), hs, g)
  | .word s :: r, hs =>
    let (o, hs', g') := fill false r hs
    (cat [([.t s g], ""), o], hs', g')
  | .glue :: r, hs => fill true r hs
  | .hole _ :: r, .out o _ :: hs =>
    let (o', hs', g') := fill false r hs
    (cat [if g then glue o else o, o'], hs', g')
  | .hole _ :: r, hs => fill g r hs
  | .choice alts :: r, .w k :: hs =>
    let (o, hs', g') := fillAlt g k alts hs
    let (o', hs'', g'') := fill g' r hs'
    (cat [o, o'], hs'', g'')
  | .choice _ :: r, hs => fill g r hs

/-- The `k`th alternative filled. -/
def fillAlt (g : Bool) : Nat → List (List Piece) → List HO → Out × List HO × Bool
  | _, [], hs => (([], ""), hs, g)
  | 0, a :: _, hs => fill g a hs
  | k + 1, _ :: r, hs => fillAlt g k r hs

end

/-- A connective's conditions: plain `a and b and c`, or comma `a, b, and c`. -/
def connective (conj : String) : ConnForm → List Out → Out
  | .plain, xs => cat (sepWords conj xs)
  | .comma, xs =>
    let n := xs.length
    cat ((xs.zipIdx).map fun (x, i) => if i == 0 then x else cat [w ",", if i == n - 1 then w conj else ([], ""), x])
  | .orIf, xs => cat ((xs.zipIdx).map fun (x, i) => if i == 0 then x else cat [w ",", w conj, w "if", x])
  | .following, xs =>
    let q := if conj == "or" then "any" else if xs.length == 2 then "both" else "all"
    cat [words (q ++ " of the following conditions are true"), w ":", english conj xs]
where
  sepWords (j : String) : List Out → List Out
    | [] => []
    | [x] => [x]
    | x :: r => x :: w j :: sepWords j r

/-- An argument list: `(a, b)`. -/
def argsOut (os : List Out) : Out := cat [w "(", cat (sepBy "," os), w ")"]

/-- An SDO's arguments: `with argument a`, `with arguments a and b`. -/
def sdoArgsOut : List Out → Out
  | [] => ([], "")
  | [x] => cat [w "with", w "argument", x]
  | xs => cat [w "with", w "arguments", english "and" xs]

/-- A list hole's parts (bullets print after the step). -/
def listOut : ListForm → List Out → Out
  | .paren, os => argsOut os
  | .comma, os => cat (sepBy "," os)
  | .english j, os => english (conjWord j) os
  | .bullets, _ => ([], "")

def codeName : Option String → Out
  | some n => cat [w "(", words n, w ")"]
  | none => ([], "")

/-- Prose: its verbatim text with variables, and what follows the step. -/
def proseOut : String × String → Out
  | (s, tr) => cat [if s.isEmpty then ([], "") else ([.raw s false], ""), after tr]

/-- The full stop after `Let`/`Return`, except after a closure literal or a step's own table (lines follow). -/
def stop (e : Expr) : Out :=
  match e with
  | .closure .. => ([], "")
  | .phrase _ [.l .bullets _] => ([], "")
  | .phrase _ hs => match hs.reverse with
    | .text _ :: .e (.table ..) :: _ => ([], "")
    | _ => w "."
  | _ => w "."

/-- An Abstract Closure literal: its words, and its pre-printed body placed one level deeper. -/
def closure (c : Ctx) (site : Nat) : Out :=
  let l := c.cl.getD site { kind := .abstract, atomic := false, params := none, caps := [], body := [] }
  cat [w "a", w "new", words (cloWords l.kind), w "with",
    (match l.params with
      | none => cat [w "no", w "parameters"]
      | some ps => cat [w "parameters", w "(", cat (sepBy "," (ps.map (var c))), w ")"]),
    w "that", w "captures",
    (if l.caps.isEmpty then w "nothing" else english "and" (l.caps.map (var c))),
    words "and performs the following steps", if l.atomic then w "atomically" else ([], ""),
    words "when called", w ":", after (indentBy (2 * (c.depth + 1)) (c.clos.getD site ""))]

/-- A phrase: its template from the table, then the holes after it. -/
def phrase (c : Ctx) (p : PhraseId) (hs : List HO) : Out :=
  let t := (c.d.phrases.getD p default).template
  let (o, rest, _) := fill false t hs
  cat (o :: rest.map fun | .out _ tr => after tr | .w _ => ([], ""))

/-- Whether `e` is a statement phrase: the List a For-each step written in its own template iterates. -/
def stepPhrase? (c : Ctx) : Expr → Bool
  | .phrase p _ => (c.d.phrases.getD p default).cat == 0
  | _ => false

/-- The description `d` of a call `WellKnownSymbol("d")`, printed `%d%`. -/
def wellKnownSym? (c : Ctx) (p : PrimId) : List Expr → Option String
  | [.val (.str s "")] => if name c.d.prims p == "WellKnownSymbol" then some s else none
  | _ => none

/-- A callee's name. -/
def calleeName (c : Ctx) : Callee → String
  | .alg a => name c.d.ops a.clause
  | .prim p => name c.d.prims p

mutual

def expr (c : Ctx) : Expr → Out
  | .var x => var c x
  | .val v => w (val c v)
  | .math .none m => w (mag m)
  | .math s m => cat [w (sign s), gw (mag m)]
  | .enum i => w ("~" ++ name c.d.enums i ++ "~")
  | .param p => w ("<sub>[" ++ name c.d.params p ++ "]</sub>")
  | .intrinsic i => w ("%" ++ name c.d.fields i ++ "%")
  | .fieldName f => w (field c f)
  | .nt n as => w ("|" ++ name c.d.nts n ++ goalText c as ++ "|")
  | .prod _ raw => w raw
  | .codeUnit _ d n => cat [w ("0x" ++ d), codeName n]
  | .codePoint _ d n => cat [w ("U+" ++ d), codeName n]
  | .code s wr => w ("`" ++ written s wr ++ "`")
  | .term s => w ("`" ++ s ++ "`")
  | .call (.alg a) xs => cat [w (name c.d.ops a.clause), glue (argsOut (exprs c xs))]
  | .call (.prim p) xs => match wellKnownSym? c p xs with
    | some s => w ("%" ++ s ++ "%")
    | none => cat [w (name c.d.prims p), glue (argsOut (exprs c xs))]
  | .callAt a xs => cat [w (name c.d.ops a.clause), glue (argsOut (exprs c xs)), words "at this Parse Node"]
  | .sdo s a x xs => cat [article a, w (name c.d.sdos s), w "of", expr c x, sdoArgsOut (exprs c xs)]
  | .component f a x => cat [article a, w (name c.d.fields f), w "of", expr c x]
  | .field x f => cat [expr c x, gw ".", gw (field c f)]
  | .imethod x m xs => cat [expr c x, gw ".", gw (field c m), glue (argsOut (exprs c xs))]
  | .cmethod x m xs => cat [expr c x, gw ".", gw (name c.d.methods m), glue (argsOut (exprs c xs))]
  | .apply f xs => cat [expr c f, glue (argsOut (exprs c xs))]
  | .index x i => cat [expr c x, gw "[", glue (expr c i), gw "]"]
  | .q x => cat [w "?", expr c x]
  | .bang x | .bangAt _ x => cat [w "!", expr c x]
  | .erratum _ _ x => expr c x
  | .un .neg x => cat [w "-", glue (expr c x)]
  | .un .not x => cat [w "not", expr c x]
  | .bin .pow x y => cat [expr c x, gw "<sup>", glue (expr c y), gw "</sup>"]
  | .bin o x y => cat [expr c x, w (binWord o), expr c y]
  | .paren x => cat [w "(", expr c x, w ")"]
  | .list xs => cat [w "«", cat (sepBy "," (exprs c xs)), w "»"]
  | .resumedWith x => cat [words "the Completion Record with which", expr c x, words "was just resumed"]
  | .thisValue bare => words (if bare then "*this* value" else "the *this* value")
  | .thisNode => words "this Parse Node"
  | .child k n s => cat [if k == 5 || k == 6 then ([], "") else w "the", (match k with
      | 0 => w "first" | 1 => w "second" | 2 => w "third" | 3 => w "derived" | 7 => w "fourth" | _ => ([], "")),
      w ("|" ++ name c.d.nts n ++ s ++ "|")]
  | .childOf _ n s => w ("|" ++ name c.d.nts n ++ s ++ "|")
  | .newTarget => w "NewTarget"
  | .table _ x => w (xref x)
  | .definition x _ => cat [words "the definition specified in", w (xref x)]
  | .tableStep _ k x => cat [words "the value that", expr c k, words "corresponds to in", w (xref x)]
  | .extreme mx x t k => cat [w "the", w (if mx then "largest" else "smallest"), ty c t, var c x, w "(",
      w "closest", w "to", w (if mx then "+∞" else "-∞"), w ")", words "such that", cond c k]
  | .record a k fs =>
    cat [article a, (match k with | some k => words (name c.d.sorts k) | none => ([], "")),
      w "{", cat (sepBy "," (fieldExprs c fs)), w "}"]
  | .annot as x =>
    cat [w ("<emu-meta" ++ String.join (as.map fun a => " " ++ attrText a) ++ ">"), glue (expr c x), gw "</emu-meta>"]
  | .xref x => w (xref x)
  | .closure site => closure c site
  | .phrase p hs => phrase c p (holes c hs)
  | .prose _ ps => proseOut (proseParts c ps)
  | .bnd x => var c x
  | .data (.sort s) => words (name c.d.sorts s)
  | .data (.choice i) => w ("choice " ++ toString i)
  | .data .absent => w "absent"
  | .ofCond x => cond c x

def exprs (c : Ctx) : List Expr → List Out
  | [] => []
  | x :: r => expr c x :: exprs c r

def fieldExprs (c : Ctx) : List (FieldId × Expr) → List Out
  | [] => []
  | (f, x) :: r => cat [w (field c f), gw ":", expr c x] :: fieldExprs c r

/-- The objectives: `, choosing them so that e is as small as possible, then so that …`. -/
def objsOut (c : Ctx) (first : Bool) : List (Bool × Expr) → Out
  | [] => ([], "")
  | o :: r => cat [w ",", words (if first then "choosing them so that" else "then so that"), objOut c o, objsOut c false r]

def objOut (c : Ctx) : Bool × Expr → Out
  | (mx, x) => cat [expr c x, words (if mx then "is as large as possible" else "is as small as possible")]

def pred (c : Ctx) : Pred → Out
  | .isVal n f vs => cat [isHead n f, alts f (exprs c vs)]
  | .isTy n f ts => cat [isHead n f, alts f (tys c ts)]
  | .phrase p hs => phrase c p (holes c hs)
  | .call f xs n => cat [w (if n then "fails" else "satisfies"), w (calleeName c f), glue (argsOut (exprs c xs))]

def conjPreds (c : Ctx) : List (Conj × Pred) → List Out
  | [] => []
  | (j, p) :: r => cat [w (conjWord j), pred c p] :: conjPreds c r

def cond (c : Ctx) : Cond → Out
  | .preds e p r => cat [expr c e, pred c p, cat (conjPreds c r)]
  | .rel o a b => cat [expr c a, w (relWord o), expr c b]
  | .and f cs => connective "and" f (conds c cs)
  | .or f cs => connective "or" f (conds c cs)
  | .paren x => cat [w "(", cond c x, w ")"]
  | .alg _ => cat [words "the following algorithm returns *true*", w ":"]
  | .phrase p hs => phrase c p (holes c hs)
  | .prose _ ps => proseOut (proseParts c ps)
  | .expr e => expr c e
  | .pass k => words k

def conds (c : Ctx) : List Cond → List Out
  | [] => []
  | x :: r => cond c x :: conds c r

def ty (c : Ctx) : TyExpr → Out
  | .sort a ms s wr => cat [if a.isEmpty then ([], "") else w a, cat (ms.map fun m => w (name c.d.sorts m)),
      words (if wr.isEmpty then name c.d.sorts s else wr)]
  | .listOf a (.record fs) => cat [if a.isEmpty then ([], "") else w a, w "List", w "of",
      words "Records with fields", english "and" (fieldTys c fs)]
  | .listOf a x => cat [if a.isEmpty then ([], "") else w a, w "List", w "of", ty c x]
  | .union f j ts => cat [
      (match f with | .either => w "either" | .oneOf => cat [w "one", w "of"] | _ => ([], "")),
      (match j, tys c ts with
        | .comma, [a, b] => cat [a, w ",", w "or", b]
        | _, os => english "or" os)]
  | .completion t => cat [words "a normal completion containing", optTy c t]
  | .interval x lo hi => cat [ty c x, words "in the inclusive interval from", expr c lo, w "to", expr c hi]
  | .value e => expr c e
  | .var a x => cat [w a, var c x]
  | .nt a n s => cat [if a.isEmpty then ([], "") else w a, w ("|" ++ name c.d.nts n ++ s ++ "|")]
  | .record fs => cat [words "a Record with fields", english "and" (fieldTys c fs)]
  | .that x p r => if isContext c x p r then ty c x else cat [ty c x, w "that", pred c p, cat (conjPreds c r)]
  | .phrase p hs => phrase c p (holes c hs)
  | .prose ps => proseOut (proseParts c ps)
  | .pred p => pred c p

def tys (c : Ctx) : List TyExpr → List Out
  | [] => []
  | x :: r => ty c x :: tys c r

def optTy (c : Ctx) : Option TyExpr → Out
  | some t => ty c t
  | none => ([], "")

def fieldTys (c : Ctx) : List (FieldId × TyExpr) → List Out
  | [] => []
  | (f, x) :: r => cat [w (field c f), w "(", ty c x, w ")"] :: fieldTys c r

def bullets (c : Ctx) : List Expr → String
  | [] => ""
  | x :: r => "\n" ++ spaces (2 * c.depth + 2) ++ "* " ++ join (expr c x).1 ++ bullets c r

def hole (c : Ctx) : Hole → HO
  | .e (.closure site) => .out (closure c site) (indentBy (2 * (c.depth + 1)) (c.clos.getD site ""))
  | .e x => .out (expr c x) ""
  | .c x => .out (cond c x) ""
  | .t x => .out (ty c x) ""
  | .b x => .out (var c x) ""
  | .bc _ x => .out (cond c x) ""
  | .w i => .w i
  | .l .bullets xs => .out ([], "") (bullets c xs)
  | .l f xs => .out (listOut f (exprs c xs)) ""
  | .text s => .out (words s) (indentBy (2 * c.depth) ("\n" ++ s))
  | .field f => .out (words (name c.d.fields f)) ""

def holes (c : Ctx) : List Hole → List HO
  | [] => []
  | h :: r => hole c h :: holes c r

def proseParts (c : Ctx) : List Part → String × String
  | [] => ("", "")
  | .text s :: r => let (a, b) := proseParts c r; (s ++ a, b)
  | .hole (.e (.var x)) :: r => let (a, b) := proseParts c r; (varText c x ++ a, b)
  | .hole h :: r =>
    let tr := match hole c h with | .out _ t => t | .w _ => ""
    let (a, b) := proseParts c r
    (a, tr ++ b)

def place (c : Ctx) : Place → Out
  | .var x => var c x
  | .field x f => cat [expr c x, gw ".", gw (field c f)]
  | .expr x => expr c x

def body (c : Ctx) : Body → Out
  | .inline s => lowerFirst (stmt c s)
  | .block ns => cat [w "then", after (nodes c.deeper ns)]

def stmt (c : Ctx) : Stmt → Out
  | .let_ x e => cat [w "Let", var c x, w "be", expr c e, stop e]
  | .letMany _ e _ => expr c e
  | .set p (.definition x true) => cat [w "Set", place c p, words "as specified in", w (xref x), w "."]
  | .set p e => cat [w "Set", place c p, w "to", expr c e, stop e]
  | .ret (some e) => cat [w "Return", expr c e, stop e]
  | .ret none => cat [w "Return", w "."]
  | .perform e => cat [w "Perform", expr c e, w "."]
  | .if_ k b _ _ => cat [w "If", cond c k, w ",", body c b]
  | .ifElse k a b => cat [w "If", cond c k, w ",", dropStop (lowerFirst (stmt c a)), w ";", w "else", lowerFirst (stmt c b)]
  | .assert k | .assertAt _ k => cat [w "Assert", w ":", cond c k, w "."]
  | .assertIf k l => cat [w "Assert", w ":", w "If", cond c k, w ",", w "then", cond c l, w "."]
  | .unreachable _ => words "Assert : This step is never reached ."
  | .throwErr i =>
    let n := name c.d.fields i
    cat [w "Throw", w (errArticle n), w ("*" ++ n ++ "*"), w "exception", w "."]
  | .throwVal e => cat [w "Throw", expr c e, w "."]
  | .note ps => cat [w "NOTE", w ":", proseOut (proseParts c ps)]
  | .repeat_ ns => cat [w "Repeat", w ",", after (nodes c.deeper ns)]
  | .repeatWhile k ns => cat [w "Repeat", w ",", w "while", cond c k, w ",", after (nodes c.deeper ns)]
  | .repeatUntil k ns => cat [w "Repeat", w ",", w "until", cond c k, w ",", after (nodes c.deeper ns)]
  | .forEach x t l r b =>
    if t.isNone && !r && stepPhrase? c l then cat [expr c l, blockAfter c b] else
    cat [w "For", w "each", (match t with | some t => ty c t | none => w "element"), var c x, w "of", expr c l, w ",",
      if r then words "in reverse List order ," else ([], ""), w "do", blockAfter c b]
  | .forEachRec fs x l b =>
    cat [words "For each Record {", cat (sepBy "," (fs.map fun f => w (field c f))), w "}", var c x, w "of",
      expr c l, w ",", w "do", blockAfter c b]
  | .forRange x lo li hi hi' d b => cat [words "For each integer", var c x, words "such that", expr c lo,
      w (if li then "≤" else "&lt;"), var c x, w (if hi' then "≤" else "&lt;"), expr c hi, w ",",
      words (if d then "in descending order ," else "in ascending order ,"), w "do", blockAfter c b]
  | .retSee e x => cat [w "Return", expr c e, w "(", w "see", w (xref x), w ")", w "."]
  | .mutate p hs => phrase c p (holes c hs)
  | .suspend e v => cat [w "Suspend", expr c e, if v == 1 then words "and remove it from the execution context stack" else ([], ""), w "."]
  | .push e _ => cat [w "Push", expr c e, words "onto the execution context stack ;", expr c e, words "is now the running execution context ."]
  | .remove e v => cat [w "Remove", expr c e, words "from the execution context stack",
      if v == 0 then words "and restore the execution context that is at the top of the execution context stack as the running execution context" else ([], ""), w "."]
  | .removeRestore e r => cat [w "Remove", expr c e, words "from the execution context stack and restore", expr c r, words "as the running execution context ."]
  | .resumeTop => words "Resume the context that is now on the top of the execution context stack as the running execution context ."
  | .resumeLet k v x as =>
    cat [if as.isEmpty then ([], "") else w ("<emu-meta" ++ String.join (as.map fun a => " " ++ attrText a) ++ ">"),
      (if as.isEmpty then w "Resume" else gw "Resume"), words "the suspended evaluation of", expr c k,
      if as.isEmpty then ([], "") else gw "</emu-meta>", w "passing", expr c v,
      words "as the result of the operation that suspended it . Let", var c x, words "be the Completion Record passed by the resumed computation ."]
  | .resume k v => cat [w "Resume", expr c k, w ",", w "passing", expr c v, w "."]
  | .setCodeState k v => cat [words "Set the code evaluation state of", expr c k,
      words "such that when evaluation is resumed for that execution context ,", expr c v, words "will be called with no arguments ."]
  | .macro a xs => cat [w (name c.d.ops a.clause), glue (argsOut (exprs c xs)), w "."]
  | .expanded a xs _ => cat [w (name c.d.ops a.clause), glue (argsOut (exprs c xs)), w "."]
  | .readings _ lit _ => stmt c lit
  | .findSuchThat x t k r f => cat [w "Find", ty c t, var c x, words "such that", cond c k, w ";",
      words "but if this is not possible (", words r, w ")", w ",", lowerFirst (stmt c f)]
  | .letSuchThat xs k os => cat [w "Let", english "and" (xs.map (var c)), w "be", w "integers", words "such that",
      cond c k, objsOut c true os, w "."]
  | .forSuchThat x t k o b => cat [w "For", w "each", ty c t, var c x, words "such that", cond c k, w ",",
      (match o with
        | some 1 => words "in descending order ,"
        | some _ => words "in ascending order ,"
        | none => ([], "")),
      w "do", blockAfter c b]
  | .forKeys x o k n b => cat [words "For each own property key", var c x, w "of", expr c o, words "such that",
      cond c k, w ",", words (match n with
        | 0 => "in ascending numeric index order"
        | 1 => "in ascending chronological order of property creation"
        | _ => "in descending numeric index order"), w ",", w "do", blockAfter c b]
  | .forIndex x l b => cat [words "For each index", var c x, w "of", expr c l, w ",", w "do", blockAfter c b]
  | .forChildren x b => cat [words "For each child node", var c x, words "of this Parse Node ,", w "do", blockAfter c b]
  | .forChildrenOf x e b => cat [words "For each child node", var c x, w "of", expr c e, w ",", w "do", blockAfter c b]
  | .repeatN e ns => cat [w "Repeat", expr c e, w "times", w ":", after (nodes c.deeper ns)]
  | .phrase p hs => phrase c p (holes c hs)
  | .prose _ ps => proseOut (proseParts c ps)
  | .withSteps s ns => cat [stmt c s, after (nodes c.deeper ns)]

def blockAfter (c : Ctx) : Body → Out
  | .block ns => after (nodes c.deeper ns)
  | .inline _ => ([], "")

/-- A numbered step: its line, the lines after it, and an If's Else if / Else steps. -/
def node (c : Ctx) : Node → String
  | .mk as (.if_ k b arms els) => line c as (stmt c (.if_ k b arms els)) ++ armsText c arms ++ optArm c els
  | .mk as (.readings e (.if_ k b arms els) alts) =>
    line c as (stmt c (.readings e (.if_ k b arms els) alts)) ++ armsText c arms ++ optArm c els
  | .mk as s => line c as (stmt c s)

def nodes (c : Ctx) : List Node → String
  | [] => ""
  | n :: r => node c n ++ nodes c r

def arm (c : Ctx) : Arm → String
  | .mk as (some k) (.block ns) => line c as (cat [w "Else", w "if", cond c k, w ",", w "then", after (nodes c.deeper ns)])
  | .mk as (some k) (.inline s) => line c as (cat [w "Else", w "if", cond c k, w ",", lowerFirst (stmt c s)])
  | .mk as none (.block ns) => line c as (cat [w "Else", w ",", after (nodes c.deeper ns)])
  | .mk as none (.inline s) => line c as (cat [w "Else", w ",", lowerFirst (stmt c s)])

def armsText (c : Ctx) : List Arm → String
  | [] => ""
  | a :: r => arm c a ++ armsText c r

def optArm (c : Ctx) : Option Arm → String
  | some a => arm c a
  | none => ""

end

/-- The closure literals' bodies, printed from column 0; a body refers only to later literals. -/
def closBodies (d : Decls) (vars : Array String) (cl : Array CloLit) : List CloLit → List String
  | [] => []
  | l :: r =>
    let t := closBodies d vars cl r
    let clos := (List.replicate (cl.size - t.length) "" ++ t).toArray
    nodes { d, vars, cl, clos, depth := 0 } l.body :: t

/-- The context of an algorithm's steps: its variables and its closure literals, their bodies printed. -/
def ctxOf (d : Decls) (vars : Array String) (cl : Array CloLit) : Ctx :=
  { d, vars, cl, clos := (closBodies d vars cl cl.toList).toArray, depth := 0 }

/-- An algorithm body: its steps, then the closing tag's indentation. -/
def body' (d : Decls) (vars : Array String) (cl : Array CloLit) (indent : Nat) (ns : List Node) : String :=
  indentBy (indent + 2) (nodes (ctxOf d vars cl) ns) ++ "\n" ++ spaces indent

/-- An algorithm's `emu-alg` body as spec.html has it. -/
def alg (d : Decls) (a : Alg) : String := body' d a.vars a.closures a.indent a.body

/-- An equation's value after `is`: a value and its `where` bindings, or two cases. -/
def eqTail (c : Ctx) : List Node → Out
  | [.mk _ (.if_ k (.inline (.ret (some e1))) [] (some (.mk _ none (.inline (.ret (some e2))))))] =>
    cat [expr c e1, w "if", cond c k, words ". Otherwise , it is", expr c e2]
  | ns =>
    match ns.reverse with
    | .mk _ (.ret (some e)) :: lets =>
      cat (expr c e :: (lets.reverse.zipIdx.map fun
        | (.mk as (.let_ x v), i) =>
          cat [if as.any (·.key == "and-bare") then ([], "") else w ",", w (if i == 0 then "where" else "and"),
            var c x, w "is", expr c v]
        | _ => ([], "")))
    | _ => ([], "")

/-- An SDO row as spec.html has it: an `emu-alg` body, or an equation bullet's content
(`The SV of <emu-grammar>…</emu-grammar> is ….` on its own line, two columns in). -/
def row (d : Decls) (r : SdoRow) : String :=
  match r.form with
  | .equation =>
    let c : Ctx := { d, vars := r.vars, cl := #[], clos := #[], depth := 0 }
    let g := fun k => w ("<emu-grammar>" ++ k ++ "</emu-grammar>")
    let gs := match r.keys with
      | [] => ([], "")
      | p :: ps => cat (g p :: ps.map fun q => cat [w "or", w "of", g q])
    let o := cat [w "The", w (name d.sdos r.sdo), w "of", gs, w "is", eqTail c r.body, w "."]
    "\n" ++ spaces (r.indent + 2) ++ join o.1 ++ "\n" ++ spaces r.indent
  | .alg as =>
    -- a row an erratum adds (`reading=` on its emu-alg) prints its reading's steps, not the chain rule
    let ns := match as.any (·.key == "reading"), r.body with
      | true, [.mk _ (.readings _ _ ((_, ns) :: _))] => ns
      | _, ns => ns
    body' d r.vars r.closures r.indent ns

end Ecma.Print
