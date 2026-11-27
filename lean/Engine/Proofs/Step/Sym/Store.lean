module

public import Engine.Proofs.Step.Sym.Prims
public import Engine.Proofs.Step.ListUpdate
public import Engine.Proofs.Maps

@[expose] public section

/-!
# Symbolic execution: the store

* `step_append`: the machine's transition at an Append to a List, its elements written with the new one, in place.
* `Keeps s t`: `t`'s heap keeps `s`'s cells (`Keeps.push`: a state with a cell allocated keeps them).
* The heap as an array: a cell pushed and then written (`setIfInBounds_push_size`), and the layout of a cell
  followed by cells allocated after it (`heap_list_get`, `heap_list_set`, `heap_rec_get`, `heap_list_get'`,
  `heap_append_set`, `heap_push_get`).
* A Record's fields are a `WMap`: `Engine.Impl.wget_put` (`Engine/Proofs/Maps.lean`) reads one after writes.
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-- The machine's transition at an Append to a List: its elements written with the new one, in place. -/
theorem step_append (X : Ctx F) (s : State F) (fr : List (Frame F)) (x : Val F) (a : Nat) (xs : Array (Val F))
    (o : Nat) (hx : x.used = x) (ha : s.heap.get a = some (.list xs o)) :
    step X ⟨s, fr, .invoke (.prim Known.pAppend [x, .ref a])⟩ =
      .inl ⟨{ s with heap := s.heap.set a (.list (xs.push x) o) }, fr, .val (.enum Known.eUnused)⟩ := by
  have hm : ([x, .ref a] : List (Val F)).map Val.used = [x, .ref a] := by
    show [x.used, (Val.ref a).used] = _
    rw [hx]; rfl
  rw [step_prim X _ Known.pAppend _ rfl (.inl rfl), prim_used _ _ rfl, hm, primOn_append]
  simp [leafV, bindR, bind, Run.bind, readCell, writeList, ha, Run.Res.bind, pure, Run.pure, Cfg.to]

/-- `t`'s heap keeps `s`'s cells. -/
def Keeps (s t : State F) : Prop := ∀ (a : Nat) (c : Cell F), s.heap.get a = some c → t.heap.get a = some c

/-- A state with a cell allocated keeps the cells. -/
theorem Keeps.push (s : State F) (d : Cell F) : Keeps s { s with heap := s.heap.push d } := by
  intro a c h
  have hlt := Engine.Model.ChunkedHeap.get_lt_next h
  have hne : a ≠ (s.heap.alloc d).1 := by simp only [Engine.Model.ChunkedHeap.alloc_fst]; omega
  rw [show (s.heap.push d).get a = s.heap.get a from Engine.Model.ChunkedHeap.alloc_get_other s.heap d a hne]
  exact h

theorem setIfInBounds_push_size {α : Type} (h : Engine.Model.ChunkedHeap α) (c d : α) :
    (h.push c).set h.next d = h.push d :=
  Engine.Model.ChunkedHeap.set_push_self h c d

theorem heap_push_get {α : Type} (h : Engine.Model.ChunkedHeap α) (r : α) :
    (h.push r).get h.next = some r :=
  Engine.Model.ChunkedHeap.alloc_get_self h r

theorem heap_list_get {α : Type} (h : Engine.Model.ChunkedHeap α) (l : α) (rs : Array α) :
    ((h.push l).pushMany rs).get h.next = some l :=
  Engine.Model.ChunkedHeap.pushMany_keeps (h.push l) rs (heap_push_get h l)

theorem heap_list_set {α : Type} (h : Engine.Model.ChunkedHeap α) (l l' : α) (rs : Array α) :
    ((h.push l).pushMany rs).set h.next l' = (h.push l').pushMany rs := by
  have hs : ((h.push l).get h.next).isSome = true := by rw [heap_push_get h l]; rfl
  rw [Engine.Model.ChunkedHeap.set_pushMany_other (h.push l) rs h.next l' hs,
      Engine.Model.ChunkedHeap.set_push_self h l l']

theorem heap_rec_get {α : Type} (h : Engine.Model.ChunkedHeap α) (l l' : α) (rs : Array α) (r : α) :
    ((h.push l').pushMany (rs.push r)).get ((h.push l).pushMany rs).next = some r := by
  rw [Engine.Model.ChunkedHeap.pushMany_push]
  have hnx : ((h.push l).pushMany rs).next = ((h.push l').pushMany rs).next := by
    simp [Engine.Model.ChunkedHeap.pushMany_next]
  rw [hnx]
  exact heap_push_get _ r

theorem heap_list_get' {α : Type} (h : Engine.Model.ChunkedHeap α) (l : α) (rs : Array α) (r : α) :
    (((h.push l).pushMany rs).push r).get h.next = some l := by
  rw [← Engine.Model.ChunkedHeap.pushMany_push]
  exact heap_list_get h l (rs.push r)

theorem heap_append_set {α : Type} (h : Engine.Model.ChunkedHeap α) (l l' : α) (rs : Array α) (r : α) :
    (((h.push l).pushMany rs).push r).set h.next l' = ((h.push l').pushMany rs).push r := by
  rw [← Engine.Model.ChunkedHeap.pushMany_push, heap_list_set, Engine.Model.ChunkedHeap.pushMany_push]

end Engine.Machine
