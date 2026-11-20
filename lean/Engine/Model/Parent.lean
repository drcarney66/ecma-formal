module

public import Engine.Model.Bare

@[expose] public section

/-!
# Accelerator: Parent at Impl

`parent` is `Model.nodeParent` at Impl: the search of the tree below the root (`parentBelow`, to the tree's
height), which meets `Ecma.Model.ParentLaws` (`Engine/Proofs/Nodes.lean`). It runs by the root's parent index
(`parentBy`): each node's key to the first node, in `parentBelow`'s order, with a child of that key; the answer
is taken where `n` is a child of that node, and the search is the fallback.

A Parse Node is its tree alone, so an index is no part of it or of the state: `treeIndex r` is `index r` and
`treeHeight r` is `r.height` (the model's `nodeHeight`), each kept in a table outside the state (by the node's key,
for that very object).

Trusted (`implemented_by`): that a kept value is the function's, and that `parentBy` by the tree's index is
`parentBelow`. `scripts/dev/parent_check.lean` compares the two at every node of sample parses.
-/

namespace Engine

open Engine.Model Ecma.Grammar
open Ecma (NtId)

/-- A Parse Node's key in a parent index. -/
def key : Node → NodeKey
  | .mk k i j _ n _ _ _ => (k, i, j, n)

/-- The parent index of the tree below `r` (to depth `f`), into `(ps, m)`: `r` is `p` (0 the root,
`k + 1` the `k`-th of `ps`); each child's key goes to `p` unless it has one, then each child's tree
in order. -/
def indexBelow : Nat → Nat → Node → Array Node × Std.HashMap NodeKey Nat →
    Array Node × Std.HashMap NodeKey Nat
  | 0, _, _, a => a
  | f + 1, p, .mk _ _ _ _ _ _ kids _, a =>
    let ks := kids.filterMap Prod.snd
    let a := ks.foldl (fun (ps, m) c => (ps, m.insertIfNew (key c) p)) a
    ks.foldl (fun (ps, m) c => indexBelow f (ps.size + 1) c (ps.push c, m)) a

/-- The parent index of the tree below `r`. -/
def index (r : Node) : Index := indexBelow (1 <<< 20) 0 r (#[], {})

/-- The parent indices built so far, by root key, each with the root it is of. -/
initialize indexCache : IO.Ref (Std.HashMap NodeKey (Node × Index)) ← IO.mkRef {}

/-- `index r`, kept: the one built for this very root where there is one. -/
unsafe def treeIndex.impl (r : Node) : Index :=
  unsafeBaseIO do
    let k := key r
    match (← indexCache.get)[k]? with
    | some (r', ix) => if ptrAddrUnsafe r' == ptrAddrUnsafe r then return ix
    | none => pure ()
    let ix := index r
    indexCache.modify (·.insert k (r, ix))
    return ix

/-- The parent index of the tree below `r`: `index r`, built once for a root and kept outside the state. -/
@[implemented_by treeIndex.impl, noinline]
def treeIndex (r : Node) : Index := index r

/-- The heights found so far, by node key, each with the node it is of. -/
initialize heightCache : IO.Ref (Std.HashMap NodeKey (Node × Nat)) ← IO.mkRef {}

/-- `r.height`, kept. -/
unsafe def treeHeight.impl (r : Node) : Nat :=
  unsafeBaseIO do
    let k := key r
    match (← heightCache.get)[k]? with
    | some (r', h) => if ptrAddrUnsafe r' == ptrAddrUnsafe r then return h
    | none => pure ()
    let h := r.height
    heightCache.modify (·.insert k (r, h))
    return h

/-- One more than the depth of the tree below `r`: `r.height`, found once for a node and kept outside the state. -/
@[implemented_by treeHeight.impl, noinline]
def treeHeight (r : Node) : Nat := r.height

/-- `parent r n` by the index `ix` of `r`'s tree and its height `h`: the node the index has for `n`'s key where
`n` is a child of it, else the search; none where the index has no such key. -/
def parentBy (ix : Index) (h : Nat) (r n : Node) : Option Node :=
  match ix with
  | (ps, m) =>
    let hit := fun (p : Node) => if (kidsOf p).any (fun c => decide (c = n)) then some p else parentBelow n h r
    match m[key n]? with
    | some 0 => hit r
    | some (k + 1) => match ps[k]? with
      | some p => hit p
      | none => parentBelow n h r
    | none => none

/-- `parent r n` by `r`'s kept index. -/
def parentFast (r n : Node) : Option Node := parentBy (treeIndex r) (treeHeight r) r n

/-- `nodeParent r n` at Impl: the search of the whole tree below `r`. It runs by `r`'s index (`parentFast`). -/
@[implemented_by parentFast]
def parent (r n : Node) : Option Node := parentBelow n r.height r

/-- `nodeAncestors r n` at Impl: the parents from `n`, as many as the tree is deep. -/
def ancestors (r n : Node) : List Node := ancestorsBy (parent r) (treeHeight r) n

end Engine
