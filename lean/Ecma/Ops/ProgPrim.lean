module

public import Ecma.Ops.Tables

@[expose] public section

/-!
# The primitives the program decides

MustCoverChild by the early-error rules, CoveredBy by a reparse, ParseGoal, InstanceOf, ChildOf, the table
lookups, the grammar's terminal alternatives, ClosureArity and ClosureKind, EvaluateBuiltin, NewRecord, and the
realm primitives (`progPrim`).
-/

namespace Ecma

variable {M : Model} (D : LeafCtx M)

/-- The alternatives of a List of grammar symbols' productions. -/
def altsOf (P : Prog) (l : Val M) : Run M (List (List GTerminal)) := do
  let .ref a := l | Run.stop .sortError
  let .list xs _ ← readCell a | Run.stop .sortError
  (M.seqFoldl (fun acc v => acc ++ [v]) [] xs).mapM fun
    | .nt k _ => optOr .residue (P.alts k)
    | _ => Run.stop .sortError

/-- §5.1.6: the code points a terminal consists of; a named code point is its value (Tables 34,
35), and `<USP>` every code point of General_Category Space_Separator (§12.2). -/
def termPoints : GTerminal → Run M (List M.Math)
  | .text s => Run.pure (s.toList.map fun c => M.ofNat c.toNat)
  | .cp n => do match (← optOr .sortError (Grammar.CodePointName.names.lookup n)).codePoint with
    | some c => Run.pure [M.ofNat c]
    | none => do
      let name := fun (s : String) => Prims.CharSets.seqOfList (M := M) (s.toList.map fun c => M.ofNat c.toNat)
      let es ← optOr .sortError (M.propSet (name "General_Category") (name "Space_Separator"))
      M.seqFoldl (fun acc e => do
        let r ← acc
        match M.eq (M.seqLen e) (M.ofNat 1), M.seqGet e (M.ofNat 0) with
        | true, some c => return r ++ [c]
        | _, _ => Run.stop .sortError) (Run.pure []) es

/-- RightHandSideCharacters(ss): a new CharSet of the characters whose code points are on the
right-hand sides of the nonterminals ss, each one terminal. TerminalAlternatives(nt): a new List
of the Strings of nt's right-hand sides, each one terminal written as code points. -/
def grammarPrim (P : Prog) (q : PrimId) (xs : List (Val M)) : Option (Run M (Val M)) :=
  if q == Known.pRightHandSideCharacters then some (match xs with
    | [l] => do
      let cs ← ((← altsOf P l).flatten).foldlM (fun acc t => do
        return (← termPoints t).foldl (fun r c => M.csAdd r (M.seqPush M.seqNil c)) acc) M.csEmpty
      Prims.CharSets.newCharSet cs
    | _ => Run.stop .sortError)
  else if q == Known.pTerminalAlternatives then some (match xs with
    | [.nt k _] => match P.alts k with
      | some ts => do
        let ss ← ts.mapM fun
          | .text s => Run.pure (Val.str (M.strLit s))
          | .cp _ => Run.stop .sortError
        listOf ss
      | none => Run.stop .residue
    | _ => Run.stop .sortError)
  else none

/-- ListFindOf(t, f, l, v): the one element of the List `l` that is a Record of the sort `t` (by its kind, a sort
the program declares a Record sort) and whose field `f` is the same as `v`; a residue for a sort that is no Record
sort, and an Assert's failure unless exactly one element is such. -/
def listFindOf (P : Prog) (k : SortId) (f : FieldId) (l v : Val M) : Run M (Val M) :=
  if !(((P.sortDef k).map (·.record)).getD false) then Run.stop .residue
  else do
    let (_, xs) ← Prims.Lists.listCell l
    let found ← Prims.Lists.foldRun (fun (acc : List (Val M)) x => do
      let isT ← match x with
        | .ref a => do
          match ← readCell a with
          | .record kd _ | .env kd _ _ => Run.pure (subSort P 64 kd k)
          | _ => Run.pure false
        | _ => Run.pure false
      if isT then do
        let y ← readField x f
        return if Val.same y v then x :: acc else acc
      else return acc) [] xs
    match found with
    | [x] => Run.pure x
    | _ => Run.stop .assertFailed

/-- The primitives the program decides: MustCoverChild by the early error rules, CoveredBy by a
reparse with the covered nonterminal's parameters (§5.1.5), ParseGoal under the readings, InstanceOf of a
sort by the sort of the node's symbol, ChildOf through the node's unit chain, the table lookups, ClosureArity and ClosureKind by the closure's literal, ListFindOf by the sorts' definitions,
EvaluateBuiltin by the function's [[Behaviour]] (a clause without an algorithm by `H`'s hook, given
*this*, the arguments List and NewTarget), NewRecord at a type value of a sort or a sort and its modifiers (`newOfTy`), the realm primitives by the realm table; none for any other. -/
def progPrim (P : Prog) (H : Host M) (q : PrimId) (xs : List (Val M)) : Option (Run M (Val M)) :=
  if q == Known.pCoveredBy then some (match xs with
    | [.nt k _, .node n] => do
      match ← reparse D.reading (← D.annexB) (P.params k) n k with
      | some (some c) => return .node c
      | some none => Run.stop .assertFailed
      | none => Run.stop .residue
    | _ => Run.stop .sortError)
  else if q == Known.pParseGoal then some (do parseGoal D.reading (← D.annexB) (xs.map Val.used))
  else if q == Known.pInstanceOf then match xs with
    | [.node n, .clause c] => some (match P.clauseProds c with
      | some ps => return .bool (ps.contains (M.nodeProd n))
      | none => Run.stop .residue)
    | [.leaf .., .clause _] => some (return .bool false)
    | _ => none
  else if q == Known.pChildNodes then some (match xs with
    | [.node nd] => listOf (childVals D nd)
    | [.leaf ..] => listOf []
    | _ => Run.stop .sortError)
  else if q == Known.pChildOf then some (match xs with
    | [.nt k _, .node n] => nodeChildOf D k n
    | _ => Run.stop .sortError)
  else if q == Known.pRightHandSideCharacters || q == Known.pTerminalAlternatives then
    grammarPrim P q (xs.map Val.used)
  else if q == Known.pClosureArity then some (match xs with
    | [.clo site _] => match P.cloOf site.alg with
      | some (cs, _) => match cs[site.idx]? with
        | some c => return .math (M.ofNat ((c.params.map List.length).getD 0))
        | none => Run.stop .sortError
      | none => Run.stop .sortError
    | _ => Run.stop .sortError)
  else if q == Known.pClosureKind then some (closureKind P xs)
  else if q == Known.pListFindOf then some (match xs with
    | [.sort k, .field f, l, v] => listFindOf P k f l v.used
    | _ => Run.stop .sortError)
  else if q == Known.pEvaluateBuiltin then some (match xs with
    | [f, this, .ref l, nt] => do
      let args ← match ← readCell l with
        | .list vs _ => Run.pure (M.seqFoldl (fun acc v => acc ++ [v]) [] vs)
        | _ => Run.stop .sortError
      let r ← Run.within (·.passed) (fun t v => { t with passed := v }) (.ref l :: ·) do
        match ← readField f Known.fBehaviour with
          | .alg a => match P.alg a with
            | some g => if g.header.kind != .builtin then Run.stop .sortError else do
              let (bs, rest) := builtinBind g.header args
              let bs ← match rest with
                | some (x, vs) => do Run.pure (bs ++ [(x, ← listOf vs)])
                | none => Run.pure bs
              let m := bs.foldl (fun m (x, _) => max m (x + 1)) 2
              -- a built-in algorithm runs as a frame of the machine (`Machine.builtinAlg`)
              let _ := (m, this, nt)
              Run.stop .residue
            | none => Run.stop .sortError
          | .clo site caps => match P.cloOf site.alg with
            | some (cs, nv) => match cs[site.idx]? with
              | some c =>
                -- a built-in closure runs as a frame of the machine (`Machine.builtinClo`)
                let _ := (c, nv, caps, args, this, nt)
                Run.stop .residue
              | none => Run.stop .sortError
            | none => Run.stop .sortError
          | .clause c => H.hookL c [this, .ref l, nt]
          | _ => Run.stop .sortError
      return retConv true r
    | _ => Run.stop .sortError)
  else Prims.Realm.prim P.realm q (xs.map Val.used)

end Ecma
