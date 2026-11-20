module

public import Debugger.View

@[expose] public section

/-!
# The JS call stack

Engine-neutral (`stackTrace {view: "js"}`): one JS frame for each execution context on
`State.stack`, found from a pause's whole spec stack (innermost first) by the push sites below.
Walking the spec frames from the outermost, a frame whose step lies past a site's push and not past
its remove holds a context more (`+1`: the next inner frames run in it), and a coroutine's frame past
its own remove one fewer (`-1`). The walk starts with the contexts its root run started under.

A JS frame has its context's function's `name` (`(anonymous)` if that is not a non-empty String), else
`(script)`, `(eval)`, `(module)`, `(iterator)` (CreateIteratorFromClosure's) or `(host)`; its JS position (the innermost node of a source's
text among its spec frames); the spec frames [lo, hi) it spans; and, for a built-in function's
context, the built-in's algorithm (`inBuiltin`).
-/

namespace Debugger

open Ecma

/-- A push site: in the algorithm `secId`, a frame at a step past `after` and not past `upTo`
(none: to the end), and not inside a closure step of `skip`, changes the contexts by `delta`;
`kind` names a context it pushes that has no function. -/
structure PushSite where
  secId : String
  after : List Nat
  upTo : Option (List Nat) := none
  skip : List (List Nat) := []
  delta : Int := 1
  kind : String := "host"

/-- The push sites, step paths outermost first (spec.html at the pinned ecma262). -/
def pushSites : List PushSite :=
  [ -- spec.html:12170 (step 9 pushes; setup only)
    { secId := "sec-initializehostdefinedrealm", after := [9] },
    -- spec.html:12450 (step 3 pushes; the resumed computation removes it before step 5)
    { secId := "sec-runsuspendedcontext", after := [3], upTo := some [4], kind := "resume" },
    -- spec.html:12469 (step 2 removes the running context; step 4 resumes the caller)
    { secId := "sec-runcallercontext", after := [2], upTo := some [4], delta := -1 },
    -- spec.html:13881 (step 12 pushes the callee's context)
    { secId := "sec-prepareforordinarycall", after := [12], kind := "call" },
    -- spec.html:13841, 13847, 13851 (step 2 pushes by PrepareForOrdinaryCall; 4.c and 7 remove)
    { secId := "sec-ecmascript-function-objects-call-thisargument-argumentslist", after := [2], upTo := some [4, 3],
      kind := "call" },
    { secId := "sec-ecmascript-function-objects-call-thisargument-argumentslist", after := [4], upTo := some [7],
      kind := "call" },
    -- spec.html:14015, 14021, 14025 (step 4 pushes by PrepareForOrdinaryCall; 6.c.i and 9 remove)
    { secId := "sec-ecmascript-function-objects-construct-argumentslist-newtarget", after := [4],
      upTo := some [6, 3, 1], kind := "call" },
    { secId := "sec-ecmascript-function-objects-construct-argumentslist-newtarget", after := [6, 3],
      upTo := some [9], kind := "call" },
    -- spec.html:14462, 14470, 14474 (step 9 pushes; 10.d and 13 remove; 10.b's closure runs elsewhere)
    { secId := "sec-builtincallorconstruct", after := [9], upTo := some [10, 4], skip := [[10, 2]], kind := "builtin" },
    { secId := "sec-builtincallorconstruct", after := [10], upTo := some [13], kind := "builtin" },
    -- spec.html:26812, 26819 (step 10 pushes; 14 removes)
    { secId := "sec-runtime-semantics-scriptevaluation", after := [10], upTo := some [14], kind := "script" },
    -- spec.html:30499, 30505 (step 27 pushes; 31 removes)
    { secId := "sec-performeval", after := [27], upTo := some [31], kind := "eval" },
    -- spec.html:29266, 29287 (step 17 pushes; 25 removes)
    { secId := "sec-source-text-module-record-initialize-environment", after := [17], upTo := some [25],
      kind := "module" },
    -- spec.html:29310, 29313 (step 3.d pushes; 3.g removes)
    { secId := "sec-source-text-module-record-execute-module", after := [3, 4], upTo := some [3, 7], kind := "module" },
    -- spec.html:29510, 29513 (step 8 pushes; 11 removes)
    { secId := "sec-smr-Evaluate", after := [8], upTo := some [11], kind := "module" },
    -- spec.html:52028, 52030 (step 13 pushes; 15 removes)
    { secId := "sec-createiteratorfromclosure", after := [13], upTo := some [15], kind := "iterator" },
    -- spec.html:51871 (the closure's step 4.f removes its own context)
    { secId := "sec-generatorstart", after := [4, 6], upTo := some [4], delta := -1 },
    -- spec.html:52222 (the closure's step 4.f removes its own context)
    { secId := "sec-asyncgeneratorstart", after := [4, 6], upTo := some [4], delta := -1 },
    -- spec.html:52575 (the closure's step 1.e removes its own context)
    { secId := "sec-asyncblockstart", after := [1, 5], upTo := some [1], delta := -1 } ]

/-- The push sites by sec-id. -/
def pushSiteTable : Std.HashMap String (List PushSite) :=
  pushSites.foldl (fun m e => m.alter e.secId fun es => some (es.getD [] ++ [e])) {}

/-- Paths (outermost first) in step order: `p` comes before `q`, a step before its sub-steps. -/
def pathLt : List Nat → List Nat → Bool
  | [], _ :: _ => true
  | a :: p, b :: q => a < b || (a == b && pathLt p q)
  | _, _ => false

/-- A frame at `p` is past step `q`: `q` and its sub-steps are done. -/
def pathPast (p q : List Nat) : Bool := !(pathLt p q || q.isPrefixOf p)

/-- What a frame at the step `path` (outermost first) of `secId` does to the contexts, and the kind
of a context it pushes. -/
def siteDelta (secId : String) (path : List Nat) : Int × String :=
  match pushSiteTable.get? secId with
  | none => ((0 : Int), "")
  | some es => es.foldl (init := ((0 : Int), "")) fun (acc : Int × String) (e : PushSite) =>
    let (d, k) := acc
    let inside := pathPast path e.after && (e.upTo.all fun q => !pathPast path q) &&
      !(e.skip.any fun s => s.isPrefixOf path && s != path)
    if inside then (d + e.delta, if e.delta > 0 then e.kind else k) else (d, k)

/-- A JS frame of the walk: the spec frames below index `top` (innermost first) down to the next
inner JS frame's are its own; the kind of the site that pushed it, none for a root's context. -/
structure JSFrame where
  top : Nat
  kind : Option String

/-- The JS frames of the spec stack `frames` (innermost first), outermost first, starting from
`base` contexts. -/
def jsFrames (n : Names) (frames : List FrameView) (base : Nat) : List JSFrame :=
  let total := frames.length
  (frames.reverse.zipIdx).foldl (init := List.replicate base { top := total, kind := none : JSFrame }) fun fs (f, i) =>
    let path := ((n.parsePath f.path).getD []).reverse
    let (d, kind) : Int × String := if f.reading.isSome then (0, "") else siteDelta f.secId path
    if d > 0 then fs ++ List.replicate d.toNat { top := total - 1 - i, kind := some kind }
    else fs.take (fs.length - (-d).toNat)

def nameKey : F.Str ⊕ F.Sym := .inl (("name".toList.map fun c => c.toNat.toUInt16).toArray)

/-- A function object's `name` own property, if it is a data property whose value is a String. -/
def fnName (s : State F) (fn : Val F) : Option String :=
  match fn with
  | .obj a => match cell? s (Show.addr a) with
    | some (.object _ ps) => match F.propsGet ps nameKey with
      | some (.ref r) => match cell? s (Show.addr r) with
        | some (.record _ fs) => match F.recGet fs Known.fValue with
          | some (.str u) => some (Show.text u)
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- Whether a function object is a built-in one: it has no [[Strict]]. -/
def isBuiltinFn (n : Names) (s : State F) (fn : Val F) : Bool :=
  match fn with
  | .obj _ => match (n.fieldId "Strict").bind (fieldOf s fn ·) with
    | some (.bool _) => false
    | _ => true
  | _ => false

/-- A context's name: its function's if not empty, else by the site that pushed it, else `(iterator)`
for a closure's generator (it has a Generator, spec.html:51861), else by its ScriptOrModule. -/
def contextName (n : Names) (st : Option (State F)) (ctx : Option (Val F)) (kind : Option String) : String :=
  let objField := fun (f : FieldId) => match st, ctx with
    | some s, some c => (fieldOf s c f).filter fun | .obj _ => true | _ => false
    | _, _ => none
  match objField Known.fFunction, st with
  | some f, some s => ((fnName s f).filter (· != "")).getD "(anonymous)"
  | _, _ =>
    if kind == some "script" || kind == some "eval" || kind == some "module" || kind == some "iterator" then
      s!"({kind.getD ""})"
    else if (objField Known.fGenerator).isSome then "(iterator)"
    else match st, ctx.bind fun c => st.bind (fieldOf · c Known.fScriptOrModule) with
      | some s, some v@(.ref _) => if (cellType n s v).endsWith "Module Record" then "(module)" else "(host)"
      | _, _ => if kind == some "call" || kind == some "builtin" then "(anonymous)" else "(host)"

/-- The JS frames as `stackTrace {view: "js"}` lists them, the running one first: id, name, JS
position (line 0 without one), `spec.frames` [lo, hi), `inBuiltin`; the context of the walk's
`j`th frame from the outermost is `State.stack`'s `j`th. -/
def jsStackJson (n : Names) (srcs : Sources) (frames : List FrameView) (st : Option (State F)) (base : Nat) :
    List Json :=
  let fs := jsFrames n frames base
  let ctxs := (st.map stackList).getD []
  let arr := frames.toArray
  let one := fun (f : JSFrame) (j : Nat) (lo : Nat) =>
    let ctx := ctxs[j]?
    let own := (List.range' lo (f.top - lo)).filterMap (arr[·]?)
    let pos := match own.findSome? fun g => g.node.bind fun nd => (srcs.ofNode? nd).map (·, nd) with
      | some (p, nd) => ("source", p.sourceJson) :: spanFields p nd
      | none => [("line", .nat 0), ("column", .nat 0)]
    let builtin := match st, ctx.bind fun c => st.bind (fieldOf · c Known.fFunction) with
      | some s, some fn => if isBuiltinFn n s fn then [("inBuiltin", Json.str ((own.getLast?.map (·.name)).getD ""))] else []
      | _, _ => []
    let spec := Json.mk ([("frames", Json.mk [("lo", .nat lo), ("hi", .nat f.top)])] ++
      (f.kind.map fun k => [("site", Json.str k)]).getD [])
    fun (id : Nat) => Json.mk ([("id", Json.nat id), ("name", .str (contextName n st ctx f.kind))] ++ pos ++ builtin ++
      [("spec", spec)])
  -- inner to outer: each frame's lo is the next inner one's top
  let (out, _) := (fs.zipIdx.reverse).foldl (init := (([] : List (Nat → Json)), 0)) fun (out, lo) (f, j) =>
    (out ++ [one f j (min lo f.top)], f.top)
  out.zipIdx.map fun (mk, i) => mk i

end Debugger
