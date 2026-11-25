module

public import Ecma.Machine.Tables

@[expose] public section

/-!
# The machine

A small-step machine over the program's code (`Prog'`), a frame per call: a call enters its
unit's code; `site` sets the step path; a statement's operands evaluate under an `args` continuation and
end in its `Fin`; every leaf operation is one `leaf` of the operands' values.
-/

namespace Ecma.Machine
open Ecma

variable {M : Model}

/-- Algorithm `a`'s code; a missing unit is residue. -/
def Ctx.algCode (X : Ctx M) (a : AlgId) : Code := (X.prog.alg a).getD [.residue "unit"]

/-- SDO `s`'s row's code at production `k`. -/
def Ctx.rowCode (X : Ctx M) (s : SdoId) (k : ProdId) : Code := (X.prog.row s k).getD [.residue "unit"]

/-- A closure literal's step path and code. -/
def Ctx.cloCode (X : Ctx M) (site : CloSite) : List Nat × Code := (X.prog.clo site).getD ([], [.residue "unit"])

/-- A frame for algorithm `g`'s steps. -/
def algFrame (g : Alg) (nd : Option M.Node) (args : List (Val M)) (rc boundary used : Bool) : Frame M :=
  ⟨g.id, nd, initSlots g.vars.size (padArgs g.header.arity args), .steps rc boundary used, [], [], none⟩

/-- Algorithm `g`'s steps in a frame of their own. -/
def enterAlg (X : Ctx M) (c : Cfg M) (g : Alg) (nd : Option M.Node) (args : List (Val M)) (rc boundary used : Bool) :
    Out M :=
  c.enter (algFrame g nd args rc boundary used) (.code (X.algCode g.id))

/-- EvaluateBuiltin of a function whose [[Behaviour]] is an Abstract Closure, passed the arguments List at
`l` (`Machine.builtinClo`). -/
def builtinClo (X : Ctx M) (c : Cfg M) (f this nt : Val M) (l : M.Addr) : Option (Out M) :=
  match M.heapGet c.s.heap l, behaviourIn c.s.heap f with
  | some (.list vs _), some (.clo site caps) => match X.P.cloOf site.alg with
    | some (cs, nv) => match cs[site.idx]? with
      | some cl =>
        let args := M.seqFoldl (fun acc v => acc ++ [v]) [] vs
        let k := (cl.params.getD []).length
        let sl := cloSlots cl nv caps (some (this, nt, .ref l))
          (args.take k ++ List.replicate (k - args.length) .missing)
        let inner := .ref l :: c.s.passed
        let (p, code) := X.cloCode site
        some ({ (c.push (.args .retC [] [])).push (.scope (.passed c.s.passed inner)) with
            s := { c.s with passed := inner } }.enter
          ⟨site.alg, none, sl, .steps false true false, p, [], some site.idx⟩ (.code code))
      | none => none
    | none => none
  | _, _ => none

/-- EvaluateBuiltin of a function whose [[Behaviour]] is a built-in algorithm (`Machine.builtinAlg`). -/
def builtinAlg (X : Ctx M) (c : Cfg M) (f this nt : Val M) (l : M.Addr) : Option (Out M) :=
  match M.heapGet c.s.heap l, behaviourIn c.s.heap f with
  | some (.list vs _), some (.alg g) => match X.P.alg g with
    | some alg =>
      if alg.header.kind != .builtin then none else
      let inner := .ref l :: c.s.passed
      some (bindR { (c.push (.args .retC [] [])).push (.scope (.passed c.s.passed inner)) with
          s := { c.s with passed := inner } }
        (builtinArgs alg.header this nt (M.seqFoldl (fun acc v => acc ++ [v]) [] vs)) fun ws c =>
        c.enter ⟨g, none, #[], .eval, [], [], none⟩ (.invoke (.alg g ws)))
    | none => none
  | _, _ => none

/-- SDO `s` at `nd` past Early Errors (`Machine.sdoEnter`). -/
def sdoEnter (X : Ctx M) (c : Cfg M) (s : SdoId) (nd : M.Node) (vs : List (Val M)) : Out M :=
  let inner := nd :: c.s.evalNodes
  let cn := { c.push (.scope (.nodes c.s.evalNodes inner)) with s := { c.s with evalNodes := inner } }
  match X.P.row s (M.nodeProd nd) with
  | some r =>
    cn.enter ⟨r.id, some nd, initSlots r.vars.size (padArgs (X.P.sdoArity s) (vs.map Val.used)),
      .steps (X.P.sdoRc s) true false, [], [], none⟩ (.code (X.rowCode s (M.nodeProd nd)))
  | none => match (X.P.sdoDefault s).bind X.P.alg with
    | some g => enterAlg X cn g (some nd) (g.args vs) g.header.rc true true
    | none => match X.P.chain (M.nodeProd nd) with
      | some k => match M.nodeChild nd k 0 with
        | some (some ch) => cn.to (.invoke (.sdo s ch vs))
        | _ => stopF c .sortError
      | none => stopF c .sortError

/-- Algorithm `a` of `vs`: its frame, else the host's hook. -/
def algEnter (X : Ctx M) (c : Cfg M) (a : AlgId) (vs : List (Val M)) : Out M :=
  match X.P.alg a with
  | some g => enterAlg X c g none (g.args vs) g.header.rc true true
  | none => leafV c (X.H.hookL a.clause vs)

/-- Table `t`'s rows after its header, each with its code (`Prog'.tstep`; none: no code). -/
def Ctx.tstepRows (X : Ctx M) (t : TableId) (tb : Table) : List (List (Option CellBody) × RowCode) :=
  let codes := (X.prog.tstep t).getD []
  tb.grid.tail.zipIdx.map fun (r, i) => (r, codes[i]?.getD {})

/-- A table step's result cell, run in the referrer's variables (`Machine.tstepRes`): a step cell's code `rc`. -/
def tstepRes (X : Ctx M) (c : Cfg M) (a : AlgId) (nd : Option M.Node) (tb : Table) (env : List (Val M))
    (rc : RowCode) : CellBody → Out M
  | .stmt _ =>
    c.enter ⟨a, nd, initSlots tb.vars.size env, .steps false false false, [], [], none⟩
      (.code (rc.res.getD [.residue "unit"]))
  | .alg g => match X.P.alg g with
    | some cg =>
      c.enter ⟨cg.id, nd, initSlots cg.vars.size env, .steps false false false, [], [], none⟩
        (.code (X.algCode g))
    | none => stopF c .sortError
  | .raw .. => stopF c .residue
  | _ => match rc.cell 1 with
    | some cc => leafV c (cellOne X cc)
    | none => stopF c .residue

/-- The rows of a table, from the first whose key cell holds `key` (`Machine.tstepRows`); a type cell's test in
an evaluation frame over the table's variables from `env`, the key bound. -/
def tstepRows (X : Ctx M) (c : Cfg M) (a : AlgId) (nd : Option M.Node) (tb : Table) (key : Val M)
    (env : List (Val M)) : List (List (Option CellBody) × RowCode) → Out M
  | [] => stopF c .assertFailed
  | (r, rc) :: rs => match cellAt r 0, cellAt r 1 with
    | some (.ty (.ty _)), some v => match rc.key with
      | some k => (c.push (.tstep a nd tb key env v rc rs)).enter ⟨a, nd, (cutVars tb.vars.size env).toArray, .eval, [], [.bind key], none⟩
          (.op k)
      | none => stopF c .residue
    | some _, some v => match rc.cell 0 with
      | some kc => bindR c (cellHas X key kc) fun b c =>
        if b then tstepRes X c a nd tb env rc v else tstepRows X c a nd tb key env rs
      | none => stopF c .residue
    | _, _ => tstepRows X c a nd tb key env rs

/-- A transfer passing `v`: the running frames are saved for the execution context the transfer suspends, and
the running execution context resumed, from its saved frames or else by calling the closure its code evaluation
state was set to. What a suspended context's calls bound in the state (the Parse Nodes being evaluated, the
arguments Lists passed) is left as the frames are saved and bound again as they resume. -/
def transferTo (c : Cfg M) (v : Val M) : Out M :=
  match c.s.suspended with
  | .ref b =>
    let s := leaveNodes c.frames c.s
    let saved := (b, c.frames) :: s.frames
    match topCtx s with
    | some (.ref a) => match savedFind a saved with
      | some fs => .inl { s := resumeNodes fs { s with frames := savedErase a saved }, frames := fs, ctl := .val v }
      | none => match M.heapGet s.heap a with
        | some (.record kind rs) => match M.recGet rs Known.fCodeState with
          | some (.clo site caps) =>
            .inl { s := { s with heap := M.heapSet s.heap a (.record kind (M.recDel rs Known.fCodeState)), frames := saved }
                   frames := [], ctl := .invoke (.clo site caps []) }
          | _ => stopF c .assertFailed
        | _ => stopF c .assertFailed
    | _ => stopF c .assertFailed
  | _ => stopF c .assertFailed

/-- A call: a frame for its unit's code, or a leaf computation (`Machine.invoke`). -/
def invoke (X : Ctx M) (c : Cfg M) : Call M → Out M
  | .alg a vs => algEnter X c a vs
  | .sdo s nd vs =>
    if s == Known.sdoEarlyErrors then
      (c.push (.args (.leaf .tupList) [] [])).to (.invoke (.early false [M.nodeProd nd] nd))
    else sdoEnter X c s nd vs
  | .clo site caps vs => match X.P.cloOf site.alg with
    | some (cs, nv) => match cs[site.idx]? with
      | some cl =>
        if cl.frame.isSome then stopF c .sortError else
        let (p, code) := X.cloCode site
        c.enter ⟨site.alg, none, cloSlots cl nv caps none (vs.map Val.used), .steps false true false, p, [], some site.idx⟩
          (.code code)
      | none => stopF c .sortError
    | none => stopF c .sortError
  | .cmethod m r vs => match r with
    | .ref a => bindR c (readCell a) fun cell c => match cell with
      | .record k _ | .env k _ _ => match X.P.method k m with
        | some g => c.to (.invoke (.alg g (r :: vs)))
        | none => stopF c .sortError
      | _ => stopF c .sortError
    | _ => stopF c .sortError
  | .callAt a nd vs => match X.P.alg a with
    | some g => enterAlg X c g (some nd) (g.args vs) g.header.rc true true
    | none => stopF c .residue
  | .prim q xs =>
    if q == Known.pMustCoverChild then match xs with
      | [.node nd, ch@(.node _)] => c.to (.invoke (.covered nd ch))
      | _ => stopF c .sortError
    else if q == Known.pNewRecord && (tyArg xs).isSome then match tyArg xs with
      | some (mods, s) =>
        bindR c (Prims.Records.newRecord [.sort (if subSort X.P 64 s Known.sList then Known.sList else s)]) fun v c =>
          ((c.push (.args (.leaf .guard) [v] [])).push (.bind v)).to (.op (sortsOp mods s))
      | none => stopF c .sortError
    else
    match q == Known.pInstanceOf, xs with
    | true, [x, .sort s] => match Prims.Nodes.symbolOf x with
      | some y => c.to (.invoke (.sort s y))
      | none => stopF c .sortError
    | _, _ =>
      let leaf : Unit → Out M := fun _ => match (if tableQ q then tablePrim X q (xs.map Val.used) else progPrim (leafCtx X) X.P X.H q xs) with
        | some r => leafV c r
        | none => leafV c (if hostPrim q then X.H.choiceL q xs else X.H.allocL q xs)
      match q == Known.pEvaluateBuiltin, xs with
      | true, [f, this, .ref l, nt] => match builtinClo X c f this nt l with
        | some o => o
        | none => match builtinAlg X c f this nt l with
          | some o => o
          | none => leaf ()
      | _, _ => leaf ()
  | .sort s v => match X.P.sortDef s with
    | some d => match d.test with
      | .alg a =>
        let test : Cfg M → Out M := fun c => (c.push (.args (.leaf .toBool) [] [])).to (.invoke (.alg a [v]))
        match v with
        | .ref r => bindR c (readCell r) fun cell c => match cell with
          | .record k _ | .env k _ _ =>
            if d.record then c.to (.val (.bool (subSort X.P 64 k s))) else test c
          | _ => if d.record then c.to (.val (.bool false)) else test c
        | _ => if d.record then c.to (.val (.bool false)) else test c
      | _ => leafV c (do return .bool (← sortTest X.P X.H (fun _ _ => Run.stop .residue) s v))
    | none => leafV c (do return .bool (← sortTest X.P X.H (fun _ _ => Run.stop .residue) s v))
  | .tstep a nd t key env => match X.P.table t with
    | some tb => tstepRows X c a nd tb key env (X.tstepRows t tb)
    | none => stopF c .sortError
  | .early tree ps nd =>
    let code := if tree then match ps with
      | [p] => X.prog.earlyTree p
      | _ => [.residue "earlyTree"]
    else X.prog.earlyOwn ps
    c.enter ⟨⟨0, 0⟩, some nd, initSlots 2 [], .steps false false false, [], [], none⟩ (.code code)
  | .earlyRow p i nd => match (X.P.early p)[i]?, X.prog.earlyRow p i with
    | some r, some (n, code) =>
      c.enter ⟨r.id, some nd, initSlots n [], .steps false false false, [], [], none⟩ (.code code)
    | _, _ => stopF c .sortError
  | .jobs clear =>
    bindR c (do
      unless M.eq (M.seqLen (← Run.get).stack) (M.ofNat 0) do Run.stop .assertFailed
      X.H.first) fun own c =>
    match own with
    | some (a, args) => (c.push (.args (.idleRan clear) [] [])).to (.invoke (.alg a args))
    | none =>
    bindR c (do
      let s ← Run.get
      unless M.eq (M.seqLen s.stack) (M.ofNat 0) do Run.stop .assertFailed
      match ← Run.hostStep (nextCall s.hostLog (X.H.elapsed s) (X.H.owns s)) X.H.nextJob with
      | none => return none
      | some k =>
        Run.hostStep (fun _ => .prepare k) (X.H.prepareJob k)
        return some (k, scheduled (← Run.get).hostLog k)) fun r c =>
    match r with
    | none => bindR c X.H.idle fun a c => match a with
      | some a => (c.push (.args (.idleRan clear) [] [])).to (.invoke (.alg a []))
      | none => c.to (.val (.enum Known.eUnused))
    | some (k, some (.clo site caps)) =>
      (c.push (.args (.jobRan clear k (.clo site caps)) [] [])).to (.invoke (.clo site caps []))
    | some _ => stopF c .sortError
  | .covered nd ch =>
    c.enter ⟨⟨0, 0⟩, some nd, #[], .eval, [], [.bind ch], none⟩ (.op (X.prog.covered (M.nodeProd nd)))

/-- An iterator's operands, evaluated before its first state. -/
def Iter.ops : Iter → List Op
  | .each l _ | .idx l | .kids (some l) | .times l => [l]
  | .range lo hi .. => [lo, hi]
  | .keys o _ _ => [o]
  | _ => []

/-- An iterator's first state from its operands' values, at the frame's Parse Node `nd`; none:
no round (a leaf's children). -/
def iterInit (nd : Option M.Node) : Iter → List (Val M) → Run M (Option (IterSt M))
  | .rep, [] | .while_ .., [] | .until_ _, [] => Run.pure (some .plain)
  | .each _ rev, [v] => do
    let l ← match v with
      | .math m => listOf [.math m]
      | v => Run.pure v
    match l with
    | .ref a =>
      if rev then do
        match ← readCell a with
        | .list xs _ => Run.pure (some (.each a (M.sub (M.seqLen xs) (M.ofNat 1)) true))
        | .block bs => Run.pure (some (.each a (M.sub (M.bytesLen bs) (M.ofNat 1)) true))
        | .charSet cs => Run.pure (some (.each a (M.sub (M.csSize cs) (M.ofNat 1)) true))
        | _ => Run.stop .sortError
      else Run.pure (some (.each a (M.ofNat 0) false))
    | _ => Run.stop .sortError
  | .range _ _ li hi desc, [.math l, .math h] =>
    let l := if li then l else M.add l (M.ofNat 1)
    let h := if hi then h else M.sub h (M.ofNat 1)
    Run.pure (some (.range (if desc then h else l) l h desc))
  | .keys _ order _, [o] => do
    match ← prim Known.pKeysOrdered [o, .math (M.ofNat order)] with
    | .ref a => Run.pure (some (.keys a (M.ofNat 0)))
    | _ => Run.stop .sortError
  | .idx _, [.ref a] => do
    match ← readCell a with
    | .list xs _ => Run.pure (some (.idx (M.ofNat 0) (M.seqLen xs)))
    | .block bs => Run.pure (some (.idx (M.ofNat 0) (M.bytesLen bs)))
    | .charSet cs => Run.pure (some (.idx (M.ofNat 0) (M.csSize cs)))
    | _ => Run.stop .sortError
  | .kids none, [] => match nd with
    | some n => Run.pure (some (.kids n 0 (M.ofNat 0)))
    | none => Run.stop .sortError
  | .kids (some _), [v] => match v with
    | .node n => Run.pure (some (.kids n 0 (M.ofNat 0)))
    | .leaf .. => Run.pure none
    | _ => Run.stop .sortError
  | .times _, [.math m] => Run.pure (some (.times (M.ofNat 0) m))
  | _, _ => Run.stop .sortError

/-- The next round's value and the iterator's state after it; none: the loop is over. -/
def iterNext (P : Prog) : IterSt M → Run M (Option (Val M × IterSt M))
  | .plain => Run.pure (some (.absent, .plain))
  | .each a i rev => do
    match ← readCell a with
    | .list xs _ =>
      if (if rev then M.lt i (M.ofNat 0) else !M.lt i (M.seqLen xs)) then Run.pure none
      else match M.seqGet xs i with
        | some v => Run.pure (some (v, .each a ((if rev then M.sub else M.add) i (M.ofNat 1)) rev))
        | none => Run.stop .sortError
    | .block bs =>
      if (if rev then M.lt i (M.ofNat 0) else !M.lt i (M.bytesLen bs)) then Run.pure none
      else match M.bytesGet bs i with
        | some b => Run.pure (some (.math b, .each a ((if rev then M.sub else M.add) i (M.ofNat 1)) rev))
        | none => Run.stop .sortError
    | .charSet cs =>
      if (if rev then M.lt i (M.ofNat 0) else !M.lt i (M.csSize cs)) then Run.pure none
      else match M.csGet cs i with
        | some sq => do return some (← Prims.CharSets.seqVal sq, .each a ((if rev then M.sub else M.add) i (M.ofNat 1)) rev)
        | none => Run.stop .sortError
    | _ => Run.stop .sortError
  | .range i lo hi desc =>
    if M.lt i lo || M.lt hi i then Run.pure none
    else Run.pure (some (.math i, .range ((if desc then M.sub else M.add) i (M.ofNat 1)) lo hi desc))
  | .keys a i => do
    match ← readCell a with
    | .list xs _ =>
      if !M.lt i (M.seqLen xs) then Run.pure none
      else match M.seqGet xs i with
        | some v => Run.pure (some (v, .keys a (M.add i (M.ofNat 1))))
        | none => Run.stop .sortError
    | _ => Run.stop .sortError
  | .idx i n => if !M.lt i n then Run.pure none else Run.pure (some (.math i, .idx (M.add i (M.ofNat 1)) n))
  | .kids nd i j => match (P.terms (M.nodeProd nd)).lookup i with
    | some t => Run.pure (some (.leaf nd i t, .kids nd (i + 1) j))
    | none =>
      let kids := M.nodeKids nd
      if !M.lt j (M.seqLen kids) then Run.pure none
      else match M.seqGet kids j with
        | some ch => Run.pure (some (.node ch, .kids nd (i + 1) (M.add j (M.ofNat 1))))
        | none => Run.stop .sortError
  | .times i n => if !M.lt i n then Run.pure none else Run.pure (some (.absent, .times (M.add i (M.ofNat 1)) n))

/-- The loop's end: the step after it, at the loop step's path. -/
def loopEnd (c : Cfg M) (l : Loop M) : Out M := (c.atPath l.p).to .done

/-- A round's body, the loop under it. -/
def loopBody (c : Cfg M) (l : Loop M) : Out M := ((c.atPath l.p).push (.loop l)).to (.code l.body)

/-- The loop's test or filter `t`, the loop under it. -/
def loopTest (c : Cfg M) (l : Loop M) (t : Op) : Out M := ((c.atPath l.p).push (.test l)).to (.op t)

/-- Loop `l` at control point `ph`: `spend` begins round `r`. -/
def loopStep (X : Ctx M) (c : Cfg M) (l : Loop M) : Phase → Out M
  | .rounds => c.to (.loop (.spend false) { l with r := 0 })
  | .spend back => c.to (.loop (if back then .jmp else .round) { l with r := l.r + 1 })
  | .jmp => c.to (.loop .round l)
  | .round => match l.it with
    | .rep | .until_ _ => loopBody c l
    | .while_ cd => loopTest c l cd
    | it => bindR c (iterNext X.P l.st) fun o c => match o with
      | none => loopEnd c l
      | some (v, st) =>
        let c := match l.x with
          | some x => c.setSlot x v
          | none => c
        match it with
        | .keys _ _ f => loopTest c { l with st } f
        | _ => loopBody c { l with st }

/-- A target's call of the operands `args`, evaluated left to right. -/
def startCall (c : Cfg M) (t : Target M) : List Op → Out M
  | [] => c.to (.invoke (t.call []))
  | o :: os => (c.push (.args (.target t) [] os)).to (.op o)

/-- An evaluated operand list, to its use. -/
def finish (X : Ctx M) (c : Cfg M) (f : Fin M) (vs : List (Val M)) : Out M :=
  match f, vs with
  | .leaf k, vs => leafV c (leaf (leafCtx X) k vs)
  | .call (.alg a), vs => c.to (.invoke (.alg a vs))
  | .call (.prim p), vs => c.to (.invoke (.prim p vs))
  | .call (.callAt a), vs => match c.top.node with
    | some nd => c.to (.invoke (.callAt a nd vs))
    | none => stopF c .sortError
  | .call (.sort s), [v] => c.to (.invoke (.sort s v))
  | .call .tyEq, [u, w] => match u with
    | .sort s => c.to (.invoke (.sort s w))
    | .ty .. => stopF c .residue
    | u => c.to (.val (.bool (Val.same w u)))
  | .call (.tstep t), [key] => c.to (.invoke (.tstep c.top.alg c.top.node t key c.top.slots.toList))
  | .call (.earlyRow p i), [] => match c.top.node with
    | some nd => c.to (.invoke (.earlyRow p i nd))
    | none => stopF c .sortError
  | .call (.earlyOwn ps), [] => match c.top.node with
    | some nd => c.to (.invoke (.early false ps nd))
    | none => stopF c .sortError
  | .call .covered, [ch] => match c.top.node with
    | some nd => c.to (.invoke (.covered nd ch))
    | none => stopF c .sortError
  | .recv .earlyTree _, [v] => match v with
    | .node nd => c.to (.invoke (.early true [M.nodeProd nd] nd))
    | _ => stopF c .sortError
  | .jobRan clear k job, [v] =>
    bindR c (do
      Run.hostStep (fun _ => .cleanup k) (X.H.cleanupJob k)
      Run.hostStep .kept X.H.clearsKept) fun kept c =>
    let c := c.push (.args (.jobKept clear v job) [] [])
    if kept then match clear with
      | some a => c.to (.invoke (.alg a []))
      | none => stopF c .residue
    else c.to (.val .absent)
  | .idleRan clear, [v] =>
    bindR c (X.H.idleEnd v) fun r c => match r with
      | none => c.to (.val (.enum Known.eUnused))
      | some false => c.to (.invoke (.jobs clear))
      | some true => bindR c (Run.hostStep .kept X.H.clearsKept) fun kept c =>
        let c := c.push (.args (.jobKept clear .absent .absent) [] [])
        if kept then match clear with
          | some a => c.to (.invoke (.alg a []))
          | none => stopF c .residue
        else c.to (.val .absent)
  | .jobKept clear v job, [_] =>
    bindR c (collectBoundary X.H) fun _ c => match v with
      | .comp t _ _ =>
        if t == Known.eNormal then c.to (.invoke (.jobs clear))
        else if jobChecked (leafCtx X) (some job) then stopF c jobStop
        else c.to (.val v)
      | _ => c.to (.invoke (.jobs clear))
  | .tupInto acc, [v] => match c.top.get acc, v with
    | .tuple a, .tuple b => (c.setSlot acc (.tuple (a ++ b))).to .done
    | _, _ => stopF c .sortError
  | .cover acc k err, [v] => match v with
    | .node n => bindR c (do reparse (← hostSections X) (X.P.params k) n k) fun r c =>
      match r with
      | some (some n') => (c.push (.args (.tupInto acc) [] [])).to (.invoke (.early true [M.nodeProd n'] n'))
      | some none => c.to (.code [.let_ acc (.leaf .tupCat [.var acc, .leaf .tuple [err]])])
      | none => stopF c .residue
    | _ => stopF c .sortError
  | .recv (.sdo s) args, [v] => match v with
    | .node nd => startCall c (.sdo s nd) args
    | _ => stopF c .sortError
  | .recv (.imethod m) args, [v] => bindR c (readField v m) fun fn c => match fn with
    | .alg a => startCall c (.alg a [v]) args
    | _ => stopF c .sortError
  | .recv (.cmethod m) args, [v] => startCall c (.cmethod m v) args
  | .recv .apply args, [v] => match v with
    | .clo site caps => startCall c (.clo site caps) args
    | .alg a => startCall c (.alg a []) args
    | .cond .. => stopF c .residue
    | _ => stopF c .sortError
  | .target t, vs => c.to (.invoke (t.call vs))
  | .bind body, [v] => (c.push (.bind v)).to (.op body)
  | .all t, [v] => match v with
    | .ref a => bindR c (readCell a) fun cell c => match cell with
      | .list xs _ => match (M.seqFoldl (fun acc x => x :: acc) [] xs).reverse with
        | [] => c.to (.val (.bool true))
        | x :: xs => ((c.push (.all t xs)).push (.bind x)).to (.op t)
      | _ => c.to (.val (.bool false))
    | _ => c.to (.val (.bool false))
  | .retC, [v] => c.to (.val (retConv true v))
  | .let_ x, [v] => (c.setSlot x v).to .done
  | .drop, _ => c.to .done
  | .ret, [v] => match c.top.kind with
    | .steps rc _ _ => c.to (.ret (retConv rc v))
    | .eval => c.to (.ret v)
  | .throw, [v] => c.to (.esc (.comp Known.eThrow v (.enum Known.eEmpty)))
  | .setField f, [o, e] => bindR c (writeField o f e) fun _ c => c.to .done
  | .setIndex e, [.ref a, .math j] => bindR c (readCell a) fun cell c => match cell with
    | .list xs o =>
      let j := M.sub j (M.ofNat o)
      if (M.seqGet xs j).isSome then (c.push (.args (.setIndexVal a xs j) [] [])).to (.op e)
      else stopF c .assertFailed
    | .block bs =>
      if (M.bytesGet bs j).isSome then (c.push (.args (.setBlockVal a j) [] [])).to (.op e)
      else stopF c .assertFailed
    | _ => stopF c .sortError
  | .setIndexVal a xs j, [v] => bindR c (writeList a (M.seqSet xs j v)) fun _ c => c.to .done
  | .setBlockVal a j, [v] => match v with
    | .math m =>
      if M.isInt m && !M.lt m (M.ofNat 0) && M.lt m (M.ofNat 256) then
        bindR c (modifyBlock a (fun bs => M.bytesSet bs j m)) fun _ c => c.to .done
      else stopF c .sortError
    | _ => stopF c .sortError
  | .br t e, [v] => withBool c v fun b => c.to (.code (if b then t else e))
  | .assert, [v] => withBool c v fun b => if b then c.to .done else stopF c .assertFailed
  | .assertAlways, [v] => withBool c v fun b => if b then c.to .done else stopF c .assertFailed
  | .assertIf d, [v] => withBool c v fun b => if b then (c.push (.args .assert [] [])).to (.op d) else c.to .done
  | .ctxPush, [v] =>
    bindR c (ctxPush X.H.exhausts v) fun _ c => c.to .done
  | .ctxRemove, [v] => bindR c (ctxRemove v) fun _ c => c.to .done
  | .ctxTopIs, [v] => match topCtx c.s with
    | some u => if Val.same u v then c.to .done else stopF c .assertFailed
    | none => stopF c .assertFailed
  | .loopInit x it p body, vs => bindR c (iterInit c.top.node it vs) fun o c => match o with
    | none => (c.atPath p).to .done
    | some st =>
      let l : Loop M := ⟨x, it, p, body, st, 0⟩
      match it with
      | .rep | .while_ .. | .until_ _ => c.to (.loop (.spend false) l)
      | _ => c.to (.loop .rounds l)
  | .transfer x, [_, v] => transferTo (c.push (.args (.resumed x) [] [])) v
  | .resumed (some x), [v] => (c.setSlot x v).to .done
  | .resumed none, [v] => { c with s := { c.s with resumed := v } }.to .done
  | _, _ => stopF c .sortError

/-- Operands `os` left to right, then `f`. -/
def startArgs (X : Ctx M) (c : Cfg M) (f : Fin M) : List Op → Out M
  | [] => finish X c f []
  | o :: os => (c.push (.args f [] os)).to (.op o)

/-- An operand tree: a leaf's value, or its operands first. -/
def evalOp (X : Ctx M) (c : Cfg M) : Op → Out M
  | .const k => leafV c (constV k)
  | .var x => leafV c (c.top.get x).read
  | .bnd x => c.to (.val (c.top.get x).binder)
  | .node => match c.top.node with
    | some nd => c.to (.val (.node nd))
    | none => stopF c .sortError
  | .child k nt => leafV c (evChild c.top.node k nt)
  | .resumed => c.to (.val c.s.resumed)
  | .closure site caps => c.to (.val (.clo ⟨c.top.alg, site⟩ (caps.map c.top.get)))
  | .bound => match c.top.bound with
    | some v => c.to (.val v)
    | none => stopF c .sortError
  | .leaf k args => startArgs X c (.leaf k) args
  | .call k args => startArgs X c (.call k) args
  | .on k recv args => (c.push (.args (.recv k args) [] [])).to (.op recv)
  | .bind e body => (c.push (.args (.bind body) [] [])).to (.op e)
  | .and [] => c.to (.val (.bool true))
  | .and (o :: os) => (c.push (.junct true os)).to (.op o)
  | .or [] => c.to (.val (.bool false))
  | .or (o :: os) => (c.push (.junct false os)).to (.op o)
  | .andT [] t => c.to (.op t)
  | .andT (o :: os) t => (c.push (.juncT os t)).to (.op o)
  | .all l t => (c.push (.args (.all t) [] [])).to (.op l)
  | .stop r => stopF c r
  | .residue _ => stopF c .residue

/-- A statement, after the code following it is pushed; it ends with `.done`, `.ret` or `.esc`. -/
def exec (X : Ctx M) (c : Cfg M) : Ins → Out M
  | .site p => (c.atPath p).to .done
  | .let_ x e => (c.push (.args (.let_ x) [] [])).to (.op e)
  | .eval e => (c.push (.args .drop [] [])).to (.op e)
  | .setField f o e => startArgs X c (.setField f) [o, e]
  | .setIndex l i e => startArgs X c (.setIndex e) [l, i]
  | .ret e => (c.push (.args .ret [] [])).to (.op e)
  | .retUnused => match c.top.kind with
    | .steps rc _ _ => c.to (.ret (retConv rc (.enum Known.eUnused)))
    | .eval => c.to (.ret (.enum Known.eUnused))
  | .throw e => (c.push (.args .throw [] [])).to (.op e)
  | .br cd t e => (c.push (.args (.br t e) [] [])).to (.op cd)
  | .assert cd => if !X.chk then c.to .done else (c.push (.args .assert [] [])).to (.op cd)
  | .assertAlways cd => (c.push (.args .assertAlways [] [])).to (.op cd)
  | .assertIf cd d => if !X.chk then c.to .done else (c.push (.args (.assertIf d) [] [])).to (.op cd)
  | .loop x it p body => startArgs X c (.loopInit x it p body) it.ops
  | .ctxPush e => (c.push (.args .ctxPush [] [])).to (.op e)
  | .ctxRemove e => (c.push (.args .ctxRemove [] [])).to (.op e)
  | .ctxTopIs e => (c.push (.args .ctxTopIs [] [])).to (.op e)
  | .transfer x ctx v => startArgs X c (.transfer x) [ctx, v]
  | .cover acc p k err => (c.push (.args (.cover acc k err) [] [])).to (.op p)
  | .stop r => stopF c r
  | .residue _ => stopF c .residue

/-- A continuation applied to a value (`.done` gives `.absent`). -/
def apply (X : Ctx M) (c : Cfg M) (k : Kont M) (v : Val M) : Out M :=
  match k with
  | .seq rest => c.to (.code rest)
  | .args f done [] => finish X c f (v :: done).reverse
  | .args f done (o :: os) => (c.push (.args f (v :: done) os)).to (.op o)
  | .junct conj cs => withBool c v fun b =>
    if b != conj then c.to (.val (.bool b))
    else match cs with
      | [] => c.to (.val (.bool b))
      | o :: os => (c.push (.junct conj os)).to (.op o)
  | .juncT cs t => withBool c v fun b =>
    if !b then c.to (.val (.bool false))
    else match cs with
      | [] => c.to (.op t)
      | o :: os => (c.push (.juncT os t)).to (.op o)
  | .all t xs => withBool c v fun b =>
    if !b then c.to (.val (.bool false))
    else match xs with
      | [] => c.to (.val (.bool true))
      | x :: xs => ((c.push (.all t xs)).push (.bind x)).to (.op t)
  | .bind _ => c.to (.val v)
  | .scope sc => { c with s := sc.ret v c.s }.to (.val v)
  | .loop l => match l.it with
    | .until_ cd => loopTest c l cd
    | _ => c.to (.loop (.spend true) l)
  | .test l => withBool c v fun b => match l.it with
    | .while_ .. => if b then loopBody c l else loopEnd c l
    | .until_ _ => if b then loopEnd c l else c.to (.loop (.spend false) l)
    | _ => if b then loopBody c l else c.to (.loop (.spend false) l)
  | .tstep a nd tb key env res rc rs => withBool c v fun b =>
    if b then tstepRes X c a nd tb env rc res else tstepRows X c a nd tb key env rs

/-- One transition; a code's last instruction runs with no `seq` pushed for the rest. -/
def step (X : Ctx M) (c : Cfg M) : Out M :=
  match c.ctl with
  | .op o => evalOp X c o
  | .code [] => c.to .done
  | .code (.site p :: is) => (c.atPath p).to (.code is)
  | .code [i] => exec X c i
  | .code (i :: is) => exec X (c.push (.seq is)) i
  | .invoke call => invoke X c call
  | .loop ph l => loopStep X c l ph
  | .val v => match c.frames with
    | f :: fs => match f.konts with
      | k :: ks => apply X { c with frames := { f with konts := ks } :: fs } k v
      | [] => match f.kind with
        | .eval => c.pop.to (.val v)
        | .steps .. => stopF c .noReturn
    | [] => .inr (.ok v c.s)
  | .done => match c.frames with
    | f :: fs => match f.konts with
      | k :: ks => apply X { c with frames := { f with konts := ks } :: fs } k .absent
      | [] => stopF c .noReturn
    | [] => todoF "done"
  | .ret v => match c.frames with
    | f :: _ => match f.kind with
      | .steps _ _ true => c.pop.to (.val (usedV v))
      | _ => c.pop.to (.val v)
    | [] => .inr (.ok v c.s)
  | .esc v => match c.frames with
    | f :: _ => match f.kind with
      | .steps _ true _ => c.to (.ret v)
      | _ => c.pop.to (.esc v)
    | [] => .inr (.esc v c.s)

end Ecma.Machine
