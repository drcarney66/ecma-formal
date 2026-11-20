module

public import Ecma.Machine.CodeTable

@[expose] public section

/-!
# The machine's configurations

The machine's state: a frame per call, its kind, Parse Node,
slots, step path and continuations. The continuations are generic: a code sequence's rest (`seq`), an
operand list and its use (`args`, the use a `Fin`), a short circuit's rest (`junct`), a List's elements
under a type (`all`), a subject's binding (`bind`, read by `Op.bound`), a scoped call's return
(`scope`), a loop's body and test (`loop`, `test`) and a table step's key test (`tstep`). A loop runs one
control point (`Phase`) at a time: its iterator's state (`IterSt`) and rounds in a `Loop`. Every leaf operation runs the one leaf table (`leaf`) over the dispatch (`subD`).
-/

namespace Ecma.Machine
open Ecma

variable {M : Model}

/-- What the machine runs: the program's code, the host, the reading chosen for each erratum (the code holds a
definition reading's steps with no choice), and whether Asserts are checked. -/
structure Ctx (M : Model) where
  prog : Prog'
  H : Host M
  rd : ErratumId → Reading
  chk : Bool

/-- The program's static fields. -/
abbrev Ctx.P (X : Ctx M) : Prog := X.prog.P

/-- A call the machine makes, with its argument values: an algorithm, an SDO at a Parse Node, a closure, an internal
method, a phrase, a primitive, a sort's test, a table step, the early errors, a cover test or the host's Jobs. -/
inductive Call (M : Model) where
  | alg (a : AlgId) (vs : List (Val M))
  | sdo (s : SdoId) (nd : M.Node) (vs : List (Val M))
  | clo (site : CloSite) (caps vs : List (Val M))
  | cmethod (m : MethodId) (r : Val M) (vs : List (Val M))
  | phrase (p : PhraseId) (nd : Option M.Node) (vs : List (Val M))
  | callAt (a : AlgId) (nd : M.Node) (vs : List (Val M))
  | prim (q : PrimId) (vs : List (Val M))
  | sort (s : SortId) (v : Val M)
  | tstep (a : AlgId) (nd : Option M.Node) (t : TableId) (key : Val M) (env : List (Val M))
  /-- the early errors of the rules of `ps` at `nd` (`tree`: of `nd` and its descendants), a tuple -/
  | early (tree : Bool) (ps : List ProdId) (nd : M.Node)
  /-- the early errors of rule row `i` of production `prod` at `nd`, a tuple -/
  | earlyRow (prod : ProdId) (i : Nat) (nd : M.Node)
  /-- whether a rule of `nd`'s production says its child `c` must cover a nonterminal -/
  | covered (nd : M.Node) (c : Val M)
  /-- the host's Jobs (§9.5), until it has none or one completes abruptly; `clear`: ClearKeptObjects -/
  | jobs (clear : Option AlgId)

/-- The target's call of the arguments. -/
def Target.call : Target M → List (Val M) → Call M
  | .sdo s nd, vs => .sdo s nd vs
  | .alg a pre, vs => .alg a (pre ++ vs)
  | .cmethod m r, vs => .cmethod m r vs
  | .clo site caps, vs => .clo site caps vs

/-- The state as control leaves the scope. -/
def Scope.leave : Scope M → State M → State M
  | .nodes o _, s => { s with evalNodes := o }
  | .passed o _, s => { s with passed := o }

/-- The state as control resumes inside the scope. -/
def Scope.resume : Scope M → State M → State M
  | .nodes _ i, s => { s with evalNodes := i }
  | .passed _ i, s => { s with passed := i }

/-- The state as the scoped call returns `v`: left. -/
def Scope.ret : Scope M → Val M → State M → State M
  | sc, _, t => sc.leave t

/-- What the machine does next. -/
inductive Ctl (M : Model) where
  | op (o : Op)
  | code (is : Code)
  | invoke (c : Call M)
  /-- loop `l` at control point `ph` -/
  | loop (ph : Phase) (l : Loop M)
  | val (v : Val M)
  | done
  | ret (v : Val M)
  | esc (c : Val M)

/-- A configuration: the state, the frames (innermost first) and the control. The frame stacks of the
execution contexts a transfer suspended are the state's (`State.frames`). -/
structure Cfg (M : Model) where
  s : State M
  frames : List (Frame M)
  ctl : Ctl M

/-- How a run ends; `xfer`: a transfer passing `v`, and what the run does when it is resumed. -/
inductive Final (M : Model) where
  | ok (v : Val M) (s : State M)
  | esc (c : Val M) (s : State M)
  | stop (r : Stop)
  | todo (form : String)

/-- A step's result: the next configuration, or the run's end. -/
abbrev Out (M : Model) := Cfg M ⊕ Final M

/-- A run of `call` from state `s`. -/
def start (s : State M) (call : Call M) : Cfg M := { s := s, frames := [], ctl := .invoke call }

/-- The Annex B overlay sections the host supports (B.1, B.3), so that their grammar applies: the host's logged
choices. -/
def hostSections (X : Ctx M) : Run M Grammar.AnnexB.Set := do
  let has := fun a => X.H.supports (X.P.overlayClause a)
  return ⟨← has .htmlLikeComments, ← has .regExpPatterns, ← has .functionDeclarationsInIfStatement,
    ← has .initializersInForIn⟩

/-- What the leaf operations read of the program and the context. -/
def leafCtx (X : Ctx M) : LeafCtx M :=
  { sub := subSort X.P 64
    unit := X.P.unit
    terms := X.P.terms
    spread := fun p => (X.P.phrase p).spreads
    overlayClause := X.P.overlayClause
    annexB := hostSections X
    reading := X.rd
    checked := X.chk
    exhausts := X.H.exhausts
    jobErratum := X.P.jobErratum }

/-- A constant's value. -/
def constV : Const → Run M (Val M)
  | .val v => valOf v
  | .math sg m => Run.pure (evMath sg m)
  | .enum e => Run.pure (.enum e)
  | .param p => Run.pure (.param p)
  | .fieldName f => Run.pure (.field f)
  | .nt k as => Run.pure (.nt k as)
  | .prod ps => Run.pure (.prod ps)
  | .nat n => Run.pure (.math (M.ofNat n))
  | .str s => Run.pure (.str (M.strLit s))
  | .term s => Run.pure (.term s)
  | .clause c => Run.pure (.clause c)
  | .table t => Run.pure (.table t)
  | .alg a => Run.pure (.alg a)
  | .data d => Run.pure d.val

/-- The leaf function `k` of its operands' values over the dispatch `D`; other operands are a sort error. -/
def leaf (D : LeafCtx M) : Leaf → List (Val M) → Run M (Val M)
  | .field f, [v] => readField v f
  | .q, [v] => question D.checked v
  | .bang, [v] => bang D.checked v
  | .bangAt r, [v] => bangAt D.checked (Stop.at D.reading r .assertFailed) v
  | .un o, [v] => unOp o v
  | .bin o, [a, b] => binOp o a b
  | .rel o, [a, b] => do return .bool (← relOp o a b)
  | .both, [.bool a, .bool b] => Run.pure (.bool (a && b))
  | .index, [a, i] => evIndex (n := 0) (evConst (Run.pure a)) (evConst (Run.pure i)) ()
  | .list, vs => listOf vs
  | .record k fs, vs => evRecord (n := 0) k (fun _ => Run.pure (fs.zip vs)) ()
  | .isVal neg nei, v :: vs => do return .bool (← isVals D neg nei v.used vs)
  | .isTy neg nei, [.bool b] => Run.pure (.bool (neg != (if nei then !b else b)))
  | .used, [v] => Run.pure v.used
  | .childOf nt, [v] => evChildOf D (n := 0) (evConst (Run.pure v)) nt ()
  | .toBool, [v] => do return .bool (← bool v)
  | .intrinsic i, [] => intrinsic i
  | .tyNt k, [v] => do return .bool (← tyNt D (n := 0) k () v)
  | .tuple, vs => Run.pure (.tuple vs)
  | .tupCat, [.tuple a, .tuple b] => Run.pure (.tuple (a ++ b))
  | .tupEmpty, [.tuple a] => Run.pure (.bool a.isEmpty)
  | .tupList, [.tuple a] => listOf a
  | .sameNode, [a, b] => Run.pure (.bool (match a with
    | .node _ => Val.same a b
    | _ => false))
  | .isNode, [v] => Run.pure (.bool (match v with
    | .node _ => true
    | _ => false))
  | .guard, [v, .bool b] => if b then Run.pure v else Run.stop .sortError
  | _, _ => Run.stop .sortError

/-- A frame's slots from the arguments, the rest unbound. -/
def initSlots (n : Nat) (args : List (Val M)) : Array (Val M) :=
  ((args.take n) ++ List.replicate (n - args.length) (Val.unbound : Val M)).toArray

/-- Slot `x`'s value; past the slots, unbound. -/
def Frame.get (f : Frame M) (x : Slot) : Val M := f.slots.getD x .unbound

/-- The subject of the innermost binding. -/
def Frame.bound (f : Frame M) : Option (Val M) :=
  f.konts.findSome? fun
    | .bind v => some v
    | _ => none

/-- A call's result as its caller sees it (`Run.used`). -/
def usedV : Val M → Val M
  | .missing => .undefined
  | .comp t .missing g => .comp t .undefined g
  | v => v

/-- `c` with control `k`. -/
def Cfg.to (c : Cfg M) (k : Ctl M) : Out M := .inl { c with ctl := k }

/-- Push a continuation on the innermost frame (on a holder frame when there is none). -/
def Cfg.push (c : Cfg M) (k : Kont M) : Cfg M :=
  match c.frames with
  | f :: fs => { c with frames := { f with konts := k :: f.konts } :: fs }
  | [] => { c with frames := [⟨⟨0, 0⟩, none, #[], .eval, [], [k], none⟩] }

/-- A stop in `c` as it leaves `c`'s frames, innermost first. -/
def Cfg.label (c : Cfg M) (q : Stop) : Stop := c.frames.foldl (fun q f => f.kind.label q) q

/-- The innermost frame (a holder frame when there is none). -/
def Cfg.top (c : Cfg M) : Frame M := c.frames.headD ⟨⟨0, 0⟩, none, #[], .eval, [], [], none⟩

/-- The innermost frame mapped by `g`. -/
def Cfg.mapTop (c : Cfg M) (g : Frame M → Frame M) : Cfg M :=
  match c.frames with
  | f :: fs => { c with frames := g f :: fs }
  | [] => c

/-- Frame `f` entered, with control `k`. -/
def Cfg.enter (c : Cfg M) (f : Frame M) (k : Ctl M) : Out M :=
  .inl { c with frames := f :: c.frames, ctl := k }

/-- The innermost frame at step path `p`. -/
def Cfg.atPath (c : Cfg M) (p : List Nat) : Cfg M := c.mapTop fun f => { f with path := p }

/-- The innermost frame's slot `x` set to `v`. -/
def Cfg.setSlot (c : Cfg M) (x : Slot) (v : Val M) : Cfg M :=
  c.mapTop fun f => { f with slots := f.slots.setIfInBounds x v }

/-- Pop the innermost frame. -/
def Cfg.pop (c : Cfg M) : Cfg M := { c with frames := c.frames.tail }

/-- The scopes of the calls running in `c`, innermost first. -/
def nodeScopes (fs : List (Frame M)) : List (Scope M) :=
  fs.flatMap fun f => f.konts.filterMap fun
    | .scope sc => some sc
    | _ => none

/-- The state as a transfer leaves the run: each scope left, innermost first. -/
def leaveNodes (fs : List (Frame M)) (s : State M) : State M := (nodeScopes fs).foldl (fun s sc => sc.leave s) s

/-- The state as a transfer resumes the run: each scope resumed, outermost first. -/
def resumeNodes (fs : List (Frame M)) (s : State M) : State M := (nodeScopes fs).foldr (fun sc t => sc.resume t) s

/-- A leaf computation's result (`bindRes`), run on the configuration's state: the configuration is taken apart
first, so that the leaf has the state's only reference and its writes are in place. -/
def bindR {α : Type} (c : Cfg M) (r : Run M α) (k : α → Cfg M → Out M) : Out M :=
  let ⟨s, fr, ctl⟩ := c
  match r s with
  | .ok a t => k a ⟨t, fr, ctl⟩
  | .esc v t => .inl ⟨t, fr, .esc v⟩
  | .stop e => .inr (.stop (fr.foldl (fun q f => f.kind.label q) e))

/-- A leaf computation's value, to the next continuation. -/
def leafV (c : Cfg M) (r : Run M (Val M)) : Out M := bindR c r fun v c => c.to (.val v)

/-- A stop at `c`, labelled by its frames. -/
def stopF (c : Cfg M) (r : Stop) : Out M := .inr (.stop (c.label r))

/-- A form the machine does not run. -/
def todoF (form : String) : Out M := .inr (.todo form)

/-- `b` from a condition's value. -/
def withBool (c : Cfg M) (v : Val M) (k : Bool → Out M) : Out M :=
  match v with
  | .bool b => k b
  | _ => stopF c .sortError

/-- Slots `xs` set in turn to their values (`CloLit.den.bind`). -/
def setSlots (sl : Array (Val M)) (xs : List (Slot × Val M)) : Array (Val M) :=
  xs.foldl (fun sl (x, v) => sl.setIfInBounds x v) sl

/-- A closure's slots: its captures, its built-in call frame, then its arguments (`CloLit.den`). -/
def cloSlots (cl : CloLit) (nv : Nat) (caps : List (Val M)) (frame : Option (Val M × Val M × Val M))
    (args : List (Val M)) : Array (Val M) :=
  let sl := setSlots (initSlots nv []) (cl.caps.zip caps)
  let sl := match cl.frame, frame with
    | some (xt, xn, xl), some (t, nt, l) => setSlots sl [(xt, t), (xn, nt), (xl, l)]
    | _, _ => sl
  let ps := cl.params.getD []
  setSlots sl (ps.zip (padArgs ps.length args))

/-- `f.[[Behaviour]]` in heap `h`, as `readField` reads it; `none` where `readField` stops. -/
def behaviourIn (h : M.Heap (Cell M)) : Val M → Option (Val M)
  | .ref a => match M.heapGet h a with
    | some (.record _ fs) | some (.env _ fs _) => M.recGet fs Known.fBehaviour
    | _ => none
  | .obj a => match M.heapGet h a with
    | some (.object sl _) => M.recGet sl Known.fBehaviour
    | _ => none
  | _ => none

/-- EvaluateBuiltin's arguments to a built-in algorithm: `this`, NewTarget, then its parameters bound from
`args` (`builtinBind`), a rest parameter's List allocated. -/
def builtinArgs (h : Header) (this nt : Val M) (args : List (Val M)) : Run M (List (Val M)) := do
  let (bs, rest) := builtinBind h args
  let bs ← match rest with
    | some (x, vs) => do Run.pure (bs ++ [(x, ← listOf vs)])
    | none => Run.pure bs
  let m := bs.foldl (fun m (x, _) => max m (x + 1)) 2
  return this :: nt :: (List.range (m - 2)).map fun i => (bs.lookup (i + 2)).getD .missing

/-- `Push ctx onto the execution context stack; ctx is now the running execution context.`: an
implementation limit when the host's resources run out (`ex`, the host's `exhausts`, read on the host's
view of the state). -/
def ctxPush (ex : State M → Bool) (c : Val M) : Run M Unit := do
  let s ← Run.get
  if ex s.hostView then Run.stop .implLimit else
  let top := (M.seqGet s.stack (M.sub (M.seqLen s.stack) (M.ofNat 1))).getD .absent
  Run.set { s with stack := M.seqPush s.stack c, suspended := top }

/-- `Remove ctx from the execution context stack`: `ctx` is the running one, and then the suspended one. -/
def ctxRemove (c : Val M) : Run M Unit := do
  let s ← Run.get
  let top := M.sub (M.seqLen s.stack) (M.ofNat 1)
  match M.seqGet s.stack top with
  | some t =>
    if Val.same t c then Run.set { s with stack := M.seqRemove s.stack top, suspended := t }
    else Run.stop .assertFailed
  | none => Run.stop .assertFailed

/-- The running execution context. -/
def topCtx (s : State M) : Option (Val M) := M.seqGet s.stack (M.sub (M.seqLen s.stack) (M.ofNat 1))

/-- The frames saved for context `a`. -/
def savedFind (a : M.Addr) : List (M.Addr × List (Frame M)) → Option (List (Frame M))
  | [] => none
  | (b, fs) :: r => if M.addrEq a b then some fs else savedFind a r

/-- The saved frames without context `a`'s. -/
def savedErase (a : M.Addr) : List (M.Addr × List (Frame M)) → List (M.Addr × List (Frame M))
  | [] => []
  | (b, fs) :: r => if M.addrEq a b then r else (b, fs) :: savedErase a r

end Ecma.Machine
