module

public import Debugger.Session
public import Engine.Machine

@[expose] public section

/-!
# The debugger's adapter to the machine: names and frame views

`names` are the machine's names for the session (`Debugger.Names`): sec-ids, algorithm and SDO names, fields,
enums, sorts, nonterminals and productions (`Ecma.Gen`), step paths as the trace writes them
(`Machine.pathText`, `parsePath`), and each algorithm's or SDO row's listing (`algorithm`): its steps
numbered as the machine numbers them (an `If`'s arms after it, a closure's steps under the step that
evaluates its literal, an erratum's readings under its step from 1) and printed as `frameText` prints
a frame's step.

`views` are a configuration's frames as the debugger shows them (`Debugger.FrameView`), under the
configurations whose steps started its run (`Parent`): each frame's step, as the source's listing has
the step its expanded step came from (`srcStep`), its slots named by its
algorithm's or SDO row's variables (as `Machine.stepText` finds them), its Parse Node, its kind, and
the machine's detail: the control (printed with `Ecma.Print` where it is syntax) and the continuations, one
line each ("hole 2 of 3 of a call to ToNumber", "seq: step 3 next", ...).
-/

namespace Debugger.Machine

open Ecma Ecma.Machine
open Engine.Machine (pathText levelText plainText ownLine stepLabel closS closC)

abbrev F := Engine.Impl

/-- The configuration a sub-run's step belongs to: its frames and control, not its state. -/
structure Parent where
  frames : List (Frame F)
  ctl : Ctl F

/-- A step path as written (`2.a.ii`, a trailing `.` allowed), innermost first: `pathText`'s
inverse. -/
def parsePath (s : String) : Option (List Nat) := parsePathBy levelText s

/-! Names. -/

def allAlgs : List Alg := Ecma.Gen.algs.flatten

def allRows : List SdoRow := Ecma.Gen.rows.flatten

/-- Every algorithm and SDO row by (clause, index), with its name: the algorithm's, or the SDO's. -/
def nameTable : Std.HashMap (Nat × Nat) String :=
  let m := allAlgs.foldl (fun m g => m.insert (g.id.clause, g.id.idx) g.name) {}
  allRows.foldl (fun m r => m.insert (r.id.clause, r.id.idx) (Ecma.Gen.sdos.getD r.sdo "?")) m

/-- Every SDO row by (clause, index). -/
def rowTable : Std.HashMap (Nat × Nat) SdoRow := allRows.foldl (fun m r => m.insert (r.id.clause, r.id.idx) r) {}

def secId (a : AlgId) : String := Ecma.Gen.clauses.getD a.clause "?"

def algName (a : AlgId) : String := nameTable.getD (a.clause, a.idx) "?"

/-- The algorithms `s` names: `sec-id#idx`, every one of a sec-id, else every one of a name. -/
def resolve (s : String) : List AlgId :=
  let all := nameTable.toList
  let ids : List (Nat × Nat) := match s.splitOn "#" with
    | [sec, idx] => match Ecma.Gen.clauses.idxOf? sec, idx.toNat? with
      | some c, some i => if nameTable.contains (c, i) then [(c, i)] else []
      | _, _ => []
    | _ => match Ecma.Gen.clauses.idxOf? s with
      | some c => (all.filter (·.1.1 == c)).map (·.1)
      | none => (all.filter (·.2 == s)).map (·.1)
  ((ids.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))).map fun (c, i) => ⟨c, i⟩).toList

def fieldIds : Std.HashMap String FieldId := Ecma.Gen.fields.zipIdx.foldl (fun m (f, i) => m.insert f i) {}

/-- A production's left-hand nonterminal, from its text (`Syntactic - LHS : …`). -/
def prodLhs (p : ProdId) : String := ((Ecma.Gen.prods.getD p "").splitOn " ").getD 2 ""

def stmtNtSet : Std.HashSet NtId :=
  Ecma.Gen.nts.zipIdx.foldl (fun m (n, i) => if stmtNtNames.contains n then m.insert i else m) {}

/-- The rows of a statement SDO on a production of a statement nonterminal. -/
def stmtRowSet : Std.HashSet (Nat × Nat) :=
  allRows.foldl (fun m r =>
    if stmtSdoNames.contains (Ecma.Gen.sdos.getD r.sdo "") && r.prods.any (stmtNtNames.contains ∘ prodLhs) then
      m.insert (r.id.clause, r.id.idx)
    else m) {}

/-- The names but the listings. -/
def baseNames : Names :=
  { secId, name := algName, resolve, pathText, parsePath, stmtRows := stmtRowSet, stmtNts := stmtNtSet,
    field := fun f => Ecma.Gen.fields.getD f "?", fieldId := fun n => fieldIds.get? n,
    enum := fun e => Ecma.Gen.enums.getD e "?", sort := fun x => Ecma.Gen.sorts.getD x "?",
    nt := fun n => Ecma.Gen.nts.getD n "?", prod := fun p => Ecma.Gen.prods.getD p "?",
    clause := fun c => Ecma.Gen.clauses.getD c "?" }

/-! Frame views. -/

/-- The steps nested one level in a step (its block, loop body, nested steps, or a closure it
defines), where a path may go on. -/
def childLists (cs : Array CloLit) : Stmt → List (List Stmt)
  | .if_ _ (.block ss) _ _ => [ss]
  | .ifElse _ s1 s2 => childLists cs s1 ++ childLists cs s2
  | .repeat_ b | .repeatWhile _ b | .repeatUntil _ b | .repeatN _ b | .block b => [b]
  | .forEach _ _ _ _ (.block b) | .forEachRec _ _ _ (.block b) | .forRange _ _ _ _ _ _ (.block b)
  | .forKeys _ _ _ _ (.block b) | .forIndex _ _ (.block b)
  | .forChildren _ (.block b) | .forChildrenOf _ _ (.block b) => [b]
  | .let_ _ (.closure k) | .perform (.closure k) | .set _ (.closure k) | .ret (some (.closure k)) =>
    (cs[k]?.map (·.body)).toList
  | _ => []

/-- The arms an `If` step numbers after itself. -/
def armsOf : Stmt → List Arm
  | .if_ _ _ arms els => arms ++ els.toList
  | _ => []

/-- The step or `Else` arm at a path (outermost first) among `ns`. -/
partial def findStep (cs : Array CloLit) (ns : List Stmt) : List Nat → Option (Stmt ⊕ Arm)
  | [] => none
  | k :: rest =>
    let rec go (i : Nat) : List Stmt → Option (Stmt ⊕ Arm)
      | [] => none
      | s :: r =>
        if k == i then
          if rest.isEmpty then some (.inl s)
          else (childLists cs s).findSome? fun ns => findStep cs ns rest
        else if k < i + width s then match (armsOf s)[k - i - 1]? with
          | some a@(.mk _ b) =>
            if rest.isEmpty then some (.inr a) else match b with
              | .block ss => findStep cs ss rest
              | .inline _ => none
          | none => none
        else go (i + width s) r
    go 1 ns

/-- A frame's algorithm or SDO row (a node-less closure frame's row): its variables, closures and steps. -/
def frameCode (P : Prog) (f : Frame F) : Array String × Array CloLit × List Stmt :=
  match f.node.bind fun _ => rowTable.get? (f.alg.clause, f.alg.idx), P.alg f.alg with
  | some r, _ => (r.vars, r.closures, r.body)
  | none, some g => (g.vars, g.closures, g.body)
  | none, none => match rowTable.get? (f.alg.clause, f.alg.idx) with
    | some r => (r.vars, r.closures, r.body)
    | none => (#[], #[], [])

/-- The text of the step at a frame's path. -/
def frameText (P : Prog) (f : Frame F) : String :=
  let (vars, cs, body) := frameCode P f
  let pc : Print.Ctx := { d := Ecma.Gen.decls, vars, cl := cs, clos := cs.map fun _ => "", depth := 0 }
  match findStep cs body f.path.reverse with
  | some (.inl n) => plainText (ownLine (Print.node pc n))
  | some (.inr a) => plainText (ownLine (Print.arm pc a))
  | none => ""

def algTable : Std.HashMap (Nat × Nat) Alg := allAlgs.foldl (fun m g => m.insert (g.id.clause, g.id.idx) g) {}

/-- A frame's source algorithm or SDO row, as its listing has it (`frameCode`'s choice). -/
def srcCode (f : Frame F) : Option (Array String × Array CloLit × List Stmt) :=
  let row := (rowTable.get? (f.alg.clause, f.alg.idx)).map fun r => (r.vars, r.closures, r.body)
  match f.node.bind fun _ => row, (algTable.get? (f.alg.clause, f.alg.idx)).map fun g => (g.vars, g.closures, g.body) with
  | some r, _ => some r
  | none, some g => some g
  | none, none => row

/-- A step `Prog.expandSuch` adds (its slot `t`): `some true` for a site's `Let t be …` (its `If` next),
`some false` for a consequent's `Let x be t[0]`. -/
def addedStep (t : Option Slot) : Stmt → Option Bool
  | .let_ x e => t.bind fun t =>
    if x == t then some true else match e with
      | .index (.var y) _ => if y == t then some false else none
      | _ => none
  | _ => none

/-- The source step an expanded step came from: path `p` (outermost first) among the expanded steps `es`
(closures `ecs`, `expandSuch`'s slot `t`) as a path (innermost first) among the source steps `ss` (closures
`scs`) numbered from `j` under `up`. An added step maps to its site, an `Else if` site's steps to its arms, and
a step with no source counterpart to its nearest step that has one. -/
partial def srcPath (ecs scs : Array CloLit) (t : Option Slot) :
    List Stmt → List Stmt → Nat → List Nat → List Nat → List Nat
  | _, _, _, up, [] => up
  | es, ss, j, up, k :: rest =>
    let rec go (i j : Nat) : List Stmt → List Stmt → List Nat
      | [], _ => up
      | s :: r, ss =>
        let added := addedStep t s
        if k < i + width s then match added, ss with
          | some true, _ :: _ => j :: up
          | some _, _ | none, [] => up
          | none, s' :: _ =>
            let p := j :: up
            if k == i then
              if rest.isEmpty then p else
                let ek := childLists ecs s
                let sk := childLists scs s'
                if ek.length != sk.length then p else
                match (ek.zip sk).find? fun (el, _) => (findStep ecs el rest).isSome with
                | some (el, sl) => srcPath ecs scs t el sl 1 p rest
                | none => p
            else
              let a := k - i - 1
              match (armsOf s)[a]?, (armsOf s')[a]? with
              | some (.mk c b), some (.mk c' b') =>
                let q := (j + 1 + a) :: up
                if rest.isEmpty then q else match c, c', b, b' with
                  | some _, some _, .block ns, .block ns' | none, none, .block ns, .block ns' =>
                    srcPath ecs scs t ns ns' 1 q rest
                  | none, some c', .block ns, _ =>
                    srcPath ecs scs t ns [.if_ c' b' ((armsOf s').drop (a + 1)) none] (j + 1 + a) up rest
                  | _, _, _, _ => q
              | _, _ => p
        else match added, ss with
          | some _, _ => go (i + width s) j r ss
          | none, [] => up
          | none, m :: ss' => go (i + width s) (j + width m) r ss'
    go 1 j es ss

/-- The source step (path innermost first, and text as its listing prints it) of path `p` (innermost first) in the
expanded code `e`, the source code being `src` (each: variables, closures, steps). -/
def srcStepIn (e src : Array String × Array CloLit × List Stmt) (p : List Nat) :
    List Nat × String :=
  let (vars, cs, body) := src
  let t := if vars.size < e.1.size then some vars.size else none
  let sp := srcPath e.2.1 cs t e.2.2 body 1 [] p.reverse
  let pc : Print.Ctx := { d := Ecma.Gen.decls, vars, cl := cs, clos := cs.map fun _ => "", depth := 0 }
  (sp, match findStep cs body sp.reverse with
    | some (.inl n) => plainText (ownLine (Print.node pc n))
    | some (.inr a) => plainText (ownLine (Print.arm pc a))
    | none => "")

/-- A frame's step as its source listing has it (`srcStepIn`); a frame with no source code, its own (`frameText`). -/
def srcStep (P : Prog) (f : Frame F) : List Nat × String :=
  match srcCode f with
  | some src => srcStepIn (frameCode P f) src f.path
  | none => (f.path, frameText P f)

def kindText : Kind → String
  | .steps .. => "steps"
  | .eval => "eval"

/-- A `steps` frame's flags: a Completion Record header (`rc`), an algorithm boundary, uses see
the result. -/
def kindFlags : Kind → List String
  | .steps rc boundary used =>
    (if rc then ["rc"] else []) ++ (if boundary then ["boundary"] else []) ++ (if used then ["used"] else [])
  | .eval => []

/-! The machine's detail: the control and the continuations. -/

def primName (q : PrimId) : String := Ecma.Gen.prims.getD q "?"

def sdoName (x : SdoId) : String := Ecma.Gen.sdos.getD x "?"

def nodeName (nd : F.Node) : String := Debugger.Show.node baseNames nd

def fieldName (f : FieldId) : String := s!"[[{Ecma.Gen.fields.getD f "?"}]]"

def callText : Call F → String
  | .alg a _ => s!"a call to {algName a}"
  | .sdo x nd _ => s!"{sdoName x} of {nodeName nd}"
  | .clo site _ _ => s!"a call to the closure {algName site.alg}#{site.idx}"
  | .cmethod m _ _ => s!"the method {Ecma.Gen.methods.getD m "?"}"
  | .callAt a nd _ => s!"a call to {algName a} at {nodeName nd}"
  | .prim q _ => s!"the primitive {primName q}"
  | .sort x _ => s!"the sort test {Ecma.Gen.sorts.getD x "?"}"
  | .tstep a _ _ _ _ => s!"a table step in {algName a}"
  | .early .. => "the early errors of a node"
  | .earlyRow .. => "an early-error rule"
  | .covered .. => "whether a child must cover a nonterminal"
  | .jobs _ => "the host's Jobs"

def leafText : Leaf → String
  | .field f => s!"read {fieldName f}"
  | .q => "? (ReturnIfAbrupt)"
  | .bang => "! (a normal completion)"
  | .un _ => "a unary operation"
  | .bin _ => "a binary operation"
  | .rel _ => "a comparison"
  | .both => "both bounds"
  | .index => "an index"
  | .list => "a List"
  | .record (some k) _ => s!"a {Ecma.Gen.sorts.getD k "?"}"
  | .record none _ => "a Record"
  | .isVal .. => "a value test"
  | .isTy .. => "a type test's answer"
  | .used => "the value as used"
  | .childOf nt => s!"the {Ecma.Gen.nts.getD nt "?"} child"
  | .toBool => "to a Boolean"
  | .intrinsic _ => "an intrinsic"
  | .tyNt k => s!"is a {Ecma.Gen.nts.getD k "?"}"
  | .tuple => "values together"
  | .tupCat => "two tuples together"
  | .tupEmpty => "whether a tuple is empty"
  | .tupList => "a List of a tuple"
  | .sameNode => "the same Parse Node"
  | .isNode => "is a nonterminal's Parse Node"
  | .guard => "the value, if the test holds"

def callKText : CallK → String
  | .alg a => s!"a call to {algName a}"
  | .prim q => s!"the primitive {primName q}"
  | .callAt a => s!"a call to {algName a} at the node"
  | .sort x => s!"the sort test {Ecma.Gen.sorts.getD x "?"}"
  | .tyEq => "a type test"
  | .tstep _ => "a table step"
  | .earlyRow .. => "an early-error rule"
  | .earlyOwn _ => "a production's early-error rules"
  | .covered => "whether a child must cover a nonterminal"

def onKText : OnK → String
  | .sdo x => sdoName x
  | .imethod m => fieldName m
  | .cmethod m => s!"the method {Ecma.Gen.methods.getD m "?"}"
  | .apply => "the function to apply"
  | .earlyTree => "the early errors of a node and its descendants"

def targetText : Target F → String
  | .sdo x nd => s!"{sdoName x} of {nodeName nd}"
  | .alg a _ => s!"a call to {algName a}"
  | .cmethod m _ => s!"the method {Ecma.Gen.methods.getD m "?"}"
  | .clo site _ => s!"a call to the closure {algName site.alg}#{site.idx}"

def iterText : Iter → String
  | .rep => "repeat"
  | .while_ .. => "repeat while"
  | .until_ _ => "repeat until"
  | .each .. => "for each"
  | .range .. => "for each integer"
  | .keys .. => "for each key"
  | .idx _ => "for each index"
  | .kids _ => "for each child"
  | .times _ => "repeat n times"

/-- What an operand list is for. -/
def finText (pc : Print.Ctx) : Fin F → String
  | .leaf k => leafText k
  | .call k => callKText k
  | .recv k _ => s!"the receiver of {onKText k}"
  | .target t => targetText t
  | .bind _ => "a subject, bound"
  | .all _ => "a List whose elements are tested"
  | .retC => "the value as a Completion Record"
  | .let_ x => s!"let {slotName pc.vars x}"
  | .drop => "drop the value"
  | .ret => "return the value"
  | .throw => "throw the value"
  | .setField f => s!"Set {fieldName f}"
  | .setIndex _ | .setIndexVal .. | .setBlockVal .. => "Set a List's element"
  | .br .. => "if: the condition"
  | .assert | .assertAlways => "assert"
  | .assertIf _ => "assert: the condition"
  | .ctxPush => "push onto the execution context stack"
  | .ctxRemove => "remove from the execution context stack"
  | .ctxTopIs => "check the running execution context"
  | .loopInit _ it p _ => s!"{iterText it}: the operands of the loop at {pathText p}"
  | .transfer _ => "a transfer"
  | .resumed (some x) => s!"the resumed completion, to {slotName pc.vars x}"
  | .resumed none => "the resumed completion"
  | .tupInto x => s!"add to {slotName pc.vars x}"
  | .cover .. => "the node that must cover a nonterminal"
  | .jobRan .. => "a Job's completion"
  | .jobKept .. => "ClearKeptObjects after a Job"
  | .idleRan .. => "the host's idle step"

/-- An operand tree, by its head. -/
def opText (pc : Print.Ctx) : Op → String
  | .const _ => "a constant"
  | .var x | .bnd x => slotName pc.vars x
  | .node => "the Parse Node"
  | .child _ nt => s!"the {Ecma.Gen.nts.getD nt "?"} child"
  | .resumed => "the resumed completion"
  | .closure k _ => s!"closure {k}"
  | .bound => "the bound subject"
  | .leaf k as => s!"{leafText k} ({as.length} operands)"
  | .call k as => s!"{callKText k} ({as.length} operands)"
  | .on k _ as => s!"{onKText k} on a receiver ({as.length} operands)"
  | .bind .. => "a subject and its test"
  | .and cs => s!"and ({cs.length})"
  | .or cs => s!"or ({cs.length})"
  | .andT cs _ => s!"and ({cs.length}), then a test"
  | .all .. => "every element of a List"
  | .stop _ => "a stop"
  | .residue form => s!"residue: {form}"

def insText (pc : Print.Ctx) : Ins → String
  | .site p => s!"step {pathText p}"
  | .let_ x _ => s!"let {slotName pc.vars x}"
  | .eval _ => "perform"
  | .setField f .. => s!"Set {fieldName f}"
  | .setIndex .. => "Set a List's element"
  | .ret _ | .retUnused => "return"
  | .throw _ => "throw"
  | .br .. => "if"
  | .assert _ | .assertAlways _ | .assertIf .. => "assert"
  | .loop _ it p _ => s!"{iterText it}: the loop at {pathText p}"
  | .ctxPush _ => "push an execution context"
  | .ctxRemove _ => "remove an execution context"
  | .ctxTopIs _ => "check the running execution context"
  | .transfer .. => "a transfer"
  | .cover .. => "must cover"
  | .stop _ => "a stop"
  | .residue form => s!"residue: {form}"

def kontText (pc : Print.Ctx) : Kont F → String
  | .seq rest => match rest with
    | i :: _ => s!"seq: {insText pc i} next ({rest.length} left)"
    | [] => "seq: the steps end"
  | .args f done todo => s!"operand {done.length + 1} of {done.length + 1 + todo.length} of {finText pc f}"
  | .junct true cs => s!"and: {cs.length} more"
  | .junct false cs => s!"or: {cs.length} more"
  | .juncT cs _ => s!"and: {cs.length} more, then a test"
  | .all _ xs => s!"every element: {xs.length} more"
  | .bind _ => "a bound subject"
  | .scope (.nodes ..) => "an SDO's return"
  | .scope (.passed ..) => "a built-in closure's return"
  | .loop l => s!"{iterText l.it}: the loop at {pathText l.p}"
  | .test l => s!"{iterText l.it}: the test of the loop at {pathText l.p}"
  | .tstep .. => "a table's rows"

def ctlText (pc : Print.Ctx) : Ctl F → String
  | .op o => "operand: " ++ opText pc o
  | .code (i :: is) => s!"code: {insText pc i} ({is.length} after)"
  | .code [] => "code: none left"
  | .invoke call => "invoke: " ++ callText call
  | .loop _ l => s!"{iterText l.it}: the loop at {pathText l.p}"
  | .val v => "value: " ++ Debugger.Show.val baseNames v
  | .done => "done"
  | .ret v => "return: " ++ Debugger.Show.val baseNames v
  | .esc v => "escape: " ++ Debugger.Show.val baseNames v

/-- A frame's view; `ctl`: the run's control, for its innermost frame. -/
def view (P : Prog) (run : Nat) (f : Frame F) (ctl : Option (Ctl F)) : FrameView :=
  let (vars, cs, _) := frameCode P f
  let pc : Print.Ctx := { d := Ecma.Gen.decls, vars, cl := cs, clos := cs.map fun _ => "", depth := 0 }
  let control := match ctl with
    | some c => ctlText pc c
    | none => "waiting for its callee"
  let (sp, text) := srcStep P f
  let (_, path) := stepLabel Ecma.Gen.clauses f.alg sp
  { alg := f.alg, secId := secId f.alg, name := algName f.alg, path,
    text, kind := kindText f.kind, run, flags := kindFlags f.kind,
    slots := f.slots.toList.zipIdx.map fun (v, i) => (slotName vars i, v), node := f.node,
    detail := some { control, konts := f.konts.map (kontText pc) } }

/-- The frames of a run's configuration (its frames and control) under the parents `ps`,
innermost first: its own, then each parent's. -/
def views (P : Prog) (ps : List Parent) (frames : List (Frame F)) (ctl : Ctl F) : List FrameView :=
  let one := fun (run : Nat) (fs : List (Frame F)) (ctl : Ctl F) =>
    fs.zipIdx.map fun (f, i) => view P run f (if i == 0 then some ctl else none)
  one ps.length frames ctl ++ (ps.zipIdx.flatMap fun (p, j) => one (ps.length - 1 - j) p.frames p.ctl)

/-! Listings. -/

mutual
/-- Steps `ns` from `i` under `up` at depth `d`, each with its sub-steps and arms. -/
partial def listNodes (pc : Print.Ctx) (d : Nat) (ns : List Stmt) (i : Nat)
    (up : List Nat) : StateM (List Nat) (List ListingStep) :=
  match ns with
  | [] => pure []
  | s :: r => do
    let p := i :: up
    let kids ← stmtKids pc (d + 1) p s
    let arms ← (armsOf s).zipIdx.mapM fun (a@(.mk cd b), j) => do
      let q := (i + 1 + j) :: up
      let ck ← closKids pc (d + 1) q ((cd.map closC).getD [])
      let bk ← bodyKids pc (d + 1) q b
      pure { path := pathText q, text := plainText (ownLine (Print.arm pc a)), depth := d, steps := ck ++ bk }
    let rest ← listNodes pc d r (i + width s) up
    pure ({ path := pathText p, text := plainText (ownLine (Print.node pc s)), depth := d, steps := kids } ::
      arms ++ rest)

/-- The sub-steps of statement `s` at path `p`: the bodies of the closures it evaluates and its nested
steps. -/
partial def stmtKids (pc : Print.Ctx) (d : Nat) (p : List Nat) (s : Stmt) :
    StateM (List Nat) (List ListingStep) := do
  let own ← closKids pc d p (closS s)
  let nested ← match s with
    | .if_ _ b _ _ | .forEach _ _ _ _ b | .forEachRec _ _ _ b | .forRange _ _ _ _ _ _ b
    | .forKeys _ _ _ _ b | .forIndex _ _ b | .forChildren _ b | .forChildrenOf _ _ b => bodyKids pc d p b
    | .ifElse _ s1 s2 => return (← stmtKids pc d p s1) ++ (← stmtKids pc d p s2)
    | .repeat_ b | .repeatWhile _ b | .repeatUntil _ b | .repeatN _ b | .block b => listNodes pc d b 1 p
    | _ => pure []
  pure (own ++ nested)

/-- A body's sub-steps at path `p`: an inline step's, or the nested steps. -/
partial def bodyKids (pc : Print.Ctx) (d : Nat) (p : List Nat) :
    Body → StateM (List Nat) (List ListingStep)
  | .inline s => stmtKids pc d p s
  | .block ns => listNodes pc d ns 1 p

/-- The bodies of the closure literals `ks` not listed yet, numbered under `p` (`Machine.cloPath`). -/
partial def closKids (pc : Print.Ctx) (d : Nat) (p : List Nat) (ks : List Nat) :
    StateM (List Nat) (List ListingStep) := do
  let mut out := []
  for k in ks do
    if (← get).contains k then continue
    modify (k :: ·)
    match pc.cl[k]? with
    | some cl => out := out ++ (← listNodes pc d cl.body 1 p)
    | none => pure ()
  return out
end

/-- Parameters' names by slot. -/
def paramNames (vars : Array String) (h : Option Header) : List String :=
  ((h.map (·.params)).getD []).map fun q => slotName vars q.x

/-- The steps of an algorithm's or SDO row's body, as its frames print them (`frameText`). -/
def listSteps (vars : Array String) (cs : Array CloLit) (body : List Stmt) : List ListingStep :=
  let pc : Print.Ctx := { d := Ecma.Gen.decls, vars, cl := cs, clos := cs.map fun _ => "", depth := 0 }
  ((listNodes pc 0 body 1 []).run []).1

/-- An SDO row's or algorithm's listing, the row first where both have the id (`algName`). -/
def algorithm (a : AlgId) : Option Listing :=
  match rowTable.get? (a.clause, a.idx), algTable.get? (a.clause, a.idx) with
  | some r, _ =>
    some {
      name := algName a, secId := secId a, idx := a.idx, kind := "row"
      production := String.intercalate " | " r.keys
      params := paramNames r.vars (Ecma.Gen.decls.sdoHeaders.getD r.sdo none)
      steps := listSteps r.vars r.closures r.body }
  | none, some g =>
    some {
      name := g.name, secId := secId a, idx := a.idx, kind := "alg"
      params := paramNames g.vars (some g.header)
      steps := listSteps g.vars g.closures g.body }
  | none, none => none

def names : Names := { baseNames with algorithm }

end Debugger.Machine
