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
    (o : Nat) (hx : x.used = x) (ha : s.heap[a]? = some (.list xs o)) :
    step X ⟨s, fr, .invoke (.prim Known.pAppend [x, .ref a])⟩ =
      .inl ⟨{ s with heap := s.heap.setIfInBounds a (.list (xs.push x) o) }, fr, .val (.enum Known.eUnused)⟩ := by
  have hm : ([x, .ref a] : List (Val F)).map Val.used = [x, .ref a] := by
    show [x.used, (Val.ref a).used] = _
    rw [hx]; rfl
  rw [step_prim X _ Known.pAppend _ rfl (.inl rfl), prim_used _ _ rfl, hm, primOn_append]
  simp [leafV, bindR, bind, Run.bind, readCell, writeList, ha, Run.Res.bind, pure, Run.pure, Cfg.to]

/-- `t`'s heap keeps `s`'s cells. -/
def Keeps (s t : State F) : Prop := ∀ (a : Nat) (c : Cell F), s.heap[a]? = some c → t.heap[a]? = some c

/-- A state with a cell allocated keeps the cells. -/
theorem Keeps.push (s : State F) (d : Cell F) : Keeps s { s with heap := s.heap.push d } := by
  intro a c h
  have hlt : a < s.heap.size := (Array.getElem?_eq_some_iff.mp h).1
  simp only [Array.getElem?_push]
  simp only [show ¬ a = s.heap.size by omega, ↓reduceIte]
  exact h

theorem setIfInBounds_push_size {α : Type} (h : Array α) (c d : α) : (h.push c).setIfInBounds h.size d = h.push d := by
  apply Array.ext_getElem?
  intro k
  by_cases hk : k = h.size
  · subst hk; simp
  · have hk' : ¬ h.size = k := fun e => hk e.symm
    simp [Array.getElem?_push, hk, hk']

theorem heap_push_get {α : Type} (h : Array α) (r : α) : (h.push r)[h.size]? = some r := by simp

theorem heap_list_get {α : Type} (h : Array α) (l : α) (rs : Array α) : ((h.push l) ++ rs)[h.size]? = some l := by
  simp [Array.getElem?_append]

theorem heap_list_set {α : Type} (h : Array α) (l l' : α) (rs : Array α) :
    ((h.push l) ++ rs).setIfInBounds h.size l' = (h.push l') ++ rs := by
  apply Array.ext_getElem?
  intro k
  simp only [Array.getElem?_setIfInBounds, Array.getElem?_append, Array.getElem?_push, Array.size_push,
    Array.size_append]
  grind

theorem heap_rec_get {α : Type} (h : Array α) (l l' : α) (rs : Array α) (r : α) :
    ((h.push l') ++ rs.push r)[((h.push l) ++ rs).size]? = some r := by
  simp

theorem heap_list_get' {α : Type} (h : Array α) (l : α) (rs : Array α) (r : α) :
    (((h.push l) ++ rs).push r)[h.size]? = some l := by
  rw [← Array.append_push]
  exact heap_list_get h l (rs.push r)

theorem heap_append_set {α : Type} (h : Array α) (l l' : α) (rs : Array α) (r : α) :
    (((h.push l) ++ rs).push r).setIfInBounds h.size l' = (h.push l') ++ rs.push r := by
  rw [← Array.append_push]
  exact heap_list_set h l l' (rs.push r)

end Engine.Machine
