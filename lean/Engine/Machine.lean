module

public import Ecma.Gen.Decls
public import Ecma.Lower.Lin
public import Engine.Machine.Trace
public import Ecma.Spec.Program
public import Engine.Accel.ListUpdate
public import Engine.Accel.Table
public import Engine.Host.Spec
public import Engine.Machine.Table

@[expose] public section

/-!
# The machine at `Impl`

The step machine (`Ecma.Machine`) over the specification's linear code at the engine's model: the program and
its code table, each unit written on first use (`Prog.memo`, `Prog'.memo`); the machine's context, with the
accelerator table's entries (`ctx`); the engine's transition (`stepE`: the store's
ceiling, then `stepA`); the run loop, which iterates it and keeps the step records (`runT`); and the runner whose
every call is a run of the loop (`dispatch`).
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-- An algorithm's id as a key: one-to-one, as `Src.algKey` is not from index 4096. -/
def idKey (a : AlgId) : Nat × Nat := (a.clause, a.idx)

/-- A table of a function's values at some keys, each computed on first use. A table is a value: it is built
where it is bound, not at each lookup. -/
structure Memo (κ β : Type) [BEq κ] [Hashable κ] where
  map : Std.HashMap κ (Thunk β)

/-- The table of `f` at `keys` (`key` one-to-one on them). -/
def Memo.of {α κ β : Type} [BEq κ] [Hashable κ] (key : α → κ) (keys : List α) (f : α → β) : Memo κ β :=
  ⟨keys.foldl (fun m a => m.insert (key a) (Thunk.mk fun _ => f a)) {}⟩

/-- The table's value at `k`, else `d ()`. -/
@[inline] def Memo.get {κ β : Type} [BEq κ] [Hashable κ] (m : Memo κ β) (k : κ) (d : Unit → β) : β :=
  match m.map[k]? with
  | some t => t.get
  | none => d ()

/-- A map from each key of `ks` to `f` at it, computed on first use. -/
def memoMap {κ α : Type} [BEq κ] [Hashable κ] (f : κ → α) (ks : List κ) : Std.HashMap κ (Thunk α) :=
  ks.foldl (fun m k => m.insert k (Thunk.mk fun _ => f k)) {}

/-- `f k` through `m` where `m` holds `k`. A lookup's arguments mention the key only in `k`, so that two lookups
compare by their keys. -/
def memoGet {κ α : Type} [BEq κ] [Hashable κ] (m : Std.HashMap κ (Thunk α)) (f : κ → α) (k : κ) : α :=
  match m[k]? with
  | some t => t.get
  | none => f k

/-- `P` with its algorithms at `as`, closure rows at `os`, SDO rows at `rs`, early-error rows at `ps` and tables
below `nt` each computed once, on first use; every other key as `P` gives it. -/
def Prog.memo (P : Prog) (as os : List AlgId) (rs : List (SdoId × ProdId)) (ps : List ProdId) (nt : Nat) : Prog :=
  let fa := fun k : Nat × Nat => P.alg ⟨k.1, k.2⟩
  let fo := fun k : Nat × Nat => P.rowOf ⟨k.1, k.2⟩
  let fr := fun k : SdoId × ProdId => P.row k.1 k.2
  let am := memoMap fa (as.map idKey)
  let om := memoMap fo (os.map idKey)
  let rm := memoMap fr rs
  let em := memoMap P.early ps
  let tm := memoMap P.table (List.range nt)
  { P with
    alg := fun a => memoGet am fa (a.clause, a.idx)
    rowOf := fun a => memoGet om fo (a.clause, a.idx)
    row := fun d p => memoGet rm fr (d, p)
    early := fun p => memoGet em P.early p
    table := fun t => memoGet tm P.table t }

/-- `Prog'.of P`, its units at `algs`, `rows` and `n` tables and the closures of `owners` each computed once (an
owner's closures together). -/
def Prog'.memo (P : Prog) (algs owners : List AlgId) (rows : List (SdoId × ProdId)) (prods : List ProdId) (n : Nat) :
    Prog' :=
  let Q := Prog'.of P
  let closOf := fun (a : AlgId) => ownerClos P a
  let alg := Memo.of idKey algs Q.alg
  let row := Memo.of id rows fun (s, k) => Q.row s k
  let clos := Memo.of idKey owners closOf
  let tstep := Memo.of id (List.range n) Q.tstep
  let rowsOf := fun (p : ProdId) => ((P.early p).zipIdx.map fun (_, i) => Q.earlyRow p i).toArray
  let earlyRows := Memo.of id prods rowsOf
  let earlyOwn := Memo.of id prods fun p => Q.earlyOwn [p]
  let covered := Memo.of id prods Q.covered
  { P := P
    alg := fun a => alg.get (idKey a) fun _ => Q.alg a
    row := fun s k => row.get (s, k) fun _ => Q.row s k
    clo := fun site => (((clos.get (idKey site.alg) fun _ => closOf site.alg))[site.idx]?).join
    tstep := fun t => tstep.get t fun _ => Q.tstep t
    earlyRow := fun p i => ((earlyRows.get p fun _ => rowsOf p)[i]?).join
    earlyOwn := fun ps => match ps with
      | [p] => earlyOwn.get p fun _ => Q.earlyOwn [p]
      | _ => Q.earlyOwn ps
    earlyTree := Q.earlyTree
    covered := fun p => covered.get p fun _ => Q.covered p
    clauseRows := Q.clauseRows }

/-- A source's algorithms, SDO rows, their owners, early rules' productions,
and tables' count. -/
def keysOf (s : Src) : List AlgId × List AlgId × List (SdoId × ProdId) × List ProdId × Nat :=
  (s.algs.map (·.id), s.rows.map (·.id), s.rows.flatMap (fun r => r.prods.map (r.sdo, ·)),
    s.earlyRows.flatMap (·.prods), s.tables.length)

/-- The specification's keys (`keysOf`). -/
def specKeys : List AlgId × List AlgId × List (SdoId × ProdId) × List ProdId × Nat := keysOf Spec.src

/-- The set-up without its shortcuts: the specification's machine alone. -/
def plain (E : Setup) : Setup :=
  { X := E.X, maxCells := E.maxCells }

/-- What the table's rows read of `P`: its Contains tables. -/
def facts (P : Prog) : Engine.Accel.Table.Facts :=
  { tab := Engine.Accel.Contains.tabOf P }

/-- The engine's set-up over `P'`: the accelerator table's rows. -/
def ctx (P' : Prog') (H : Host F) (chk : Bool) : Setup :=
  Setup.ofTable (Engine.Accel.Table.fastTable (facts P'.P)) P' H chk

/-- The program's units (`unitOf`), each found once, on first use: `rows` the source's SDO rows (id, SDO,
productions), `keys` the algorithms' and rows' ids. -/
def unitsMemo (P : Prog) (rows : List (AlgId × SdoId × List ProdId)) (keys : List AlgId) :
    Units :=
  let sdoOf : Std.HashMap (Nat × Nat × ProdId) SdoId := rows.foldl (fun m (a, s, ks) =>
    ks.foldl (fun m k => m.insert (a.clause, a.idx, k) s) m) {}
  let rowAt := fun (a : AlgId) (k : ProdId) => (sdoOf[(a.clause, a.idx, k)]?).bind fun s => P.row s k
  { own := (Memo.of idKey keys fun a => unitOf P rowAt a none).map
    ownAt := (Memo.of (fun (x : AlgId × ProdId) => (x.1.clause, x.1.idx, x.2))
      (rows.flatMap fun (a, _, ks) => ks.map (a, ·)) fun (a, k) => unitOf P rowAt a (some k)).map
    other := fun a prod => unitOf P rowAt a prod }

/-- The specification's SDO rows: each one's id, SDO and productions. -/
def specRows : List (AlgId × SdoId × List ProdId) := Spec.src.rows.map fun r => (r.id, r.sdo, r.prods)

unsafe def traceOut.impl (l : String) (k : Unit → Out F) : Out F := dbgTrace l k

/-- `k`, after printing the line `l` on stderr. -/
@[implemented_by traceOut.impl]
def traceOut (_l : String) (k : Unit → Out F) : Out F := k ()

/-- `k`, after printing the line of the step `c` enters on stderr; not a step of the driver's own algorithms. -/
@[inline] def traced (units : Thunk Units) (c : Cfg F) (k : Unit → Out F) : Out F :=
  if (c.frames.head?.map fun f => Engine.Host.driverAlg f.alg).getD false then k () else
  match stepLine Ecma.Gen.decls units Ecma.Gen.clauses c with
  | some l => traceOut l k
  | none => k ()

unsafe def noteOut.impl (fs : List (Frame F)) (o : Out F) : Out F :=
  match o with
  | .inr (.stop _) | .inr (.todo _) => unsafeBaseIO do
    stopFrames.modify fun r => some (r.getD #[] ++ (fs.map fun f => (f.alg, f.path)).toArray)
    return o
  | _ => unsafeBaseIO do
    if (← stopFrames.get).isSome then stopFrames.set none
    return o

/-- `o`, a transition's result from the frames `fs`: a stop's frames kept, another's dropped. -/
@[implemented_by noteOut.impl]
def noteOut (_fs : List (Frame F)) (o : Out F) : Out F := o

unsafe def noteStep.impl (units : Thunk Units) (e : Option (AlgId × Option Nat × Option ProdId × List Nat))
    (o : Out F) : Out F :=
  match e with
  | some (a, clo, prod, p) => unsafeBaseIO do
    let isAssert := match (units.get.of a prod).at clo p with
      | some (.inl n) => assertStep n
      | _ => false
    coverSteps.modify (·.insert (a.clause, a.idx, p) isAssert)
    return o
  | none => o

/-- `o`, a transition's result, the step `e` it enters kept. -/
@[implemented_by noteStep.impl]
def noteStep (_units : Thunk Units) (_e : Option (AlgId × Option Nat × Option ProdId × List Nat)) (o : Out F) : Out F := o

instance : Inhabited (Final F) := ⟨.stop .residue⟩

/-- One transition of the engine: a stop with an implementation limit where the store is past the set-up's
ceiling, else `stepA`. -/
def stepE (E : Setup) (c : Cfg F) : Out F :=
  if E.full c then .inr (.stop .implLimit) else stepA E c

/-- `stepE`, keeping what `ob` asks for: the trace's line, a stop's frames, the step entered. -/
@[inline] def stepObs (E : Setup) (units : Thunk Units) (ob : Obs) (c : Cfg F) : Out F :=
  if E.full c then .inr (.stop .implLimit) else
  let fs := c.frames
  let e := if ob.cover then entered c else none
  let k := fun _ => stepA E c
  let o := if ob.trace then traced units c k else k ()
  let o := if ob.sites then noteOut fs o else o
  if ob.cover then noteStep units e o else o

/-- A run: transitions from `c` until the machine ends, keeping what `ob` asks for. This is the loop: the
machine's `step` has none. A run that does not end does not return; `none` is never the result. -/
def runT (E : Setup) (units : Thunk Units) (ob : Obs) (c : Cfg F) : Option (Final F) :=
  match stepObs E units ob c with
  | .inl c => runT E units ob c
  | .inr f => some f
partial_fixpoint

/-- A run's end as a computation's result. -/
def Final.toRes : Final F → Res F (Val F)
  | .ok v s => .ok v s
  | .esc c s => .esc c s
  | .stop r => .stop r
  | .todo _ => .stop .residue

/-- The runner over the runs `go`: a call is a run of the machine from it. -/
def dispatchBy (E : Setup) (go : Cfg F → Final F) : Engine.Host.Runner :=
  { call := fun a vs s => Final.toRes (go (start s (.alg a vs)))
    clo := fun site caps vs s => Final.toRes (go (start s (.clo site caps vs)))
    jobs := fun clear s => Final.toRes (go (start s (.jobs clear)))
    leaf := leafCtx E.X }

/-- The dispatcher whose every entry is a run of the loop (`runT`; the residue stop for the `none` it never
returns). -/
def dispatch (E : Setup) (units : Thunk Units) (ob : Obs) : Engine.Host.Runner :=
  dispatchBy E fun c => (runT E units ob c).getD (.stop .residue)

end Engine.Machine

namespace Engine

open Ecma Engine.SpecHost

/-- The host's algorithms' ids. -/
def hostIds : List AlgId :=
  [printAlg, detachAlg, createRealmAlg, evalScriptAlg, isHTMLDDAAlg, loaderAlg] ++ agentAlgs.toList.map (·.id) ++ firstAlgs.toList.map (·.id)

/-- The program: the specification's with the host's algorithms (`hostAlgs`), expanded (`Src.expanded`), each
algorithm, row and table rewritten once (`Prog.memo`, at `Machine.specKeys` and the host's ids). -/
def P : Prog :=
  Machine.Prog.memo (Ecma.Spec.src.expanded hostAlgs) (Machine.specKeys.1 ++ hostIds) Machine.specKeys.2.1
    Machine.specKeys.2.2.1 Machine.specKeys.2.2.2.1 Machine.specKeys.2.2.2.2

/-- The linear code of `P`, each unit written once. -/
@[noinline] def P' : Ecma.Machine.Prog' :=
  let (algs, owners, rows, prods, n) := Machine.specKeys
  Machine.Prog'.memo P (algs ++ hostIds) owners rows prods n

end Engine
