module

public import Engine.Machine
public import Ecma.Machine.Run
public import Engine.Proofs.Step.Sym.Prims

@[expose] public section

/-!
# The List updates in place

`Engine.Accel.ListUpdate.prim`'s four entries (Append, Prepend, "Add e to S", ReplaceElem) are the
specification's primitives: `prim_eq`, and `prim_step`, the engine's transition at one is the machine's
(`step_prim`: an instance of `step_prim_plain`).
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-- The machine's transition at a call of a primitive that is neither the program's nor the host's: the
primitive's run. -/
theorem step_prim (X : Ctx F) (c : Cfg F) (q : PrimId) (xs : List (Val F)) (hc : c.ctl = .invoke (.prim q xs))
    (hq : q = Known.pAppend ∨ q = Known.pPrepend ∨ q = Known.pSetAdd ∨ q = Known.pReplaceElem) :
    step X c = leafV c (Ecma.prim q xs) := by
  refine step_prim_plain X c q xs hc ?_ ?_ <;> rcases hq with h | h | h | h <;> subst h <;> rfl

open Engine.Accel.ListUpdate in
/-- The update in place of a List cell is the write of its elements. -/
theorem modifyIn_eq (a : Nat) (f : Array (Val F) → Array (Val F)) (s : State F) :
    modifyIn a f s = match s.heap[a]? with
      | some (.list xs o) => .ok true { s with heap := s.heap.setIfInBounds a (.list (f xs) o) }
      | some _ => .ok false s
      | none => .stop .sortError := by
  unfold modifyIn take
  dsimp only
  split <;> simp_all

theorem primOn_append (x : Val F) (a : Nat) : primOn Known.pAppend [x, .ref a] = (do
    match ← readCell a with
    | .list xs _ => do writeList a (F.seqPush xs x); return .enum Known.eUnused
    | _ => Run.stop .sortError : Run F (Val F)) := by
  unfold primOn
  simp (config := { decide := true }) only [↓reduceIte]
  funext s
  simp only [bind, Run.bind, readCell]
  generalize s.heap[a]? = o
  cases o with
  | none => rfl
  | some c => cases c <;> rfl

theorem primOn_prepend (x : Val F) (a : Nat) : primOn Known.pPrepend [x, .ref a] = (do
    match ← readCell a with
    | .list xs _ => do writeList a (F.seqCons x xs); return .enum Known.eUnused
    | _ => Run.stop .sortError : Run F (Val F)) := by
  unfold primOn
  simp (config := { decide := true }) only [↓reduceIte]
  funext s
  simp only [bind, Run.bind, readCell]
  generalize s.heap[a]? = o
  cases o with
  | none => rfl
  | some c => cases c <;> rfl

theorem primOn_setAdd (ys : List (Val F)) : primOn Known.pSetAdd ys = Prims.Lists.setAdd ys := rfl

theorem primOn_replaceElem (ys : List (Val F)) : primOn Known.pReplaceElem ys = Prims.Lists.replaceElem ys := rfl

theorem prim_used (q : PrimId) (xs : List (Val F)) (h : (q == Known.pPresent) = false) :
    Ecma.prim q xs = primOn q (xs.map Val.used) := by simp [Ecma.prim, h]

open Engine.Accel.ListUpdate in
theorem appendIn_eq (x : Val F) (a : Nat) : appendIn x a = primOn Known.pAppend [x, .ref a] := by
  rw [primOn_append]
  funext s
  simp only [appendIn, bind, Run.bind, modifyIn_eq, readCell, writeList]
  cases h : s.heap[a]? with
  | none => simp [h, Run.Res.bind]
  | some c => cases c <;> simp [h, Run.Res.bind, Run.bind, Run.stop, pure, Run.pure, writeList]

open Engine.Accel.ListUpdate in
theorem prependIn_eq (x : Val F) (a : Nat) : prependIn x a = primOn Known.pPrepend [x, .ref a] := by
  rw [primOn_prepend]
  funext s
  simp only [prependIn, bind, Run.bind, modifyIn_eq, readCell, writeList]
  cases h : s.heap[a]? with
  | none => simp [h, Run.Res.bind]
  | some c => cases c <;> simp [h, Run.Res.bind, Run.bind, Run.stop, pure, Run.pure, writeList]

/-- A run that reads: it returns in the state it started from, or stops. -/
def Reads {α : Type} (m : Run F α) : Prop := ∀ s, (∃ a, m s = .ok a s) ∨ (∃ r, m s = .stop r)

theorem Reads.pure {α : Type} (a : α) : Reads (Run.pure a : Run F α) := fun _ => .inl ⟨a, rfl⟩

theorem Reads.bind {α β : Type} {m : Run F α} {f : α → Run F β} (hm : Reads m) (hf : ∀ a, Reads (f a)) :
    Reads (Run.bind m f) := by
  intro s
  rcases hm s with ⟨a, h⟩ | ⟨r, h⟩
  · simp only [Run.bind, h, Run.Res.bind]
    exact hf a s
  · exact .inr ⟨r, by simp [Run.bind, h, Run.Res.bind]⟩

theorem Reads.readCell (a : Nat) : Reads (readCell a : Run F (Cell F)) := by
  intro s
  unfold Ecma.readCell
  cases F.heapGet s.heap a with
  | none => exact .inr ⟨_, rfl⟩
  | some c => exact .inl ⟨c, rfl⟩

theorem Reads.sameElem (x y : Val F) : Reads (Prims.Lists.sameElem x y) := by
  unfold Prims.Lists.sameElem
  split
  · split
    · exact Reads.pure _
    · refine Reads.bind (Reads.readCell _) fun c => Reads.bind (Reads.readCell _) fun d => ?_
      split <;> exact Reads.pure _
  · exact Reads.pure _

theorem Reads.seqFold {β γ : Type} {f : β → γ → Run F β} (hf : ∀ b x, Reads (f b x)) (b : β) (xs : Array γ) :
    Reads (Run.seqFold f b xs) := by
  intro s
  unfold Run.seqFold
  show (∃ a, Array.foldl _ _ xs = _) ∨ (∃ r, Array.foldl _ _ xs = _)
  rw [← Array.foldl_toList]
  generalize xs.toList = l
  suffices h : ∀ (r : Res F β), ((∃ a, r = .ok a s) ∨ ∃ e, r = .stop e) →
      (∃ a, List.foldl (fun r x => Run.Res.bind r fun b => f b x) r l = .ok a s) ∨
        ∃ e, List.foldl (fun r x => Run.Res.bind r fun b => f b x) r l = .stop e from h _ (.inl ⟨b, rfl⟩)
  induction l with
  | nil => exact fun r h => h
  | cons x l ih =>
    intro r h
    refine ih _ ?_
    rcases h with ⟨a, rfl⟩ | ⟨e, rfl⟩
    · exact hf a x s
    · exact .inr ⟨e, rfl⟩

theorem Reads.hasElem (x : Val F) (xs : Array (Val F)) : Reads (Prims.Lists.hasElem x xs) := by
  unfold Prims.Lists.hasElem Prims.Lists.foldRun
  refine Reads.seqFold (fun b v => ?_) _ _
  split
  · exact Reads.pure _
  · exact Reads.sameElem _ _

theorem Reads.elemSeq? (v : Val F) : Reads (Prims.CharSets.elemSeq? v) := by
  intro s
  unfold Prims.CharSets.elemSeq?
  split
  · exact .inl ⟨_, rfl⟩
  · refine Reads.bind (Reads.readCell _) (fun c => ?_) s
    cases c <;> exact fun _ => .inl ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩

theorem Reads.elemSeq (v : Val F) : Reads (Prims.CharSets.elemSeq v) := by
  intro s
  unfold Prims.CharSets.elemSeq
  show (∃ a, Run.Res.bind (Prims.CharSets.elemSeq? v s) (fun o => optOr Stop.sortError o) = .ok a s) ∨
    ∃ r, Run.Res.bind (Prims.CharSets.elemSeq? v s) (fun o => optOr Stop.sortError o) = .stop r
  rcases Reads.elemSeq? v s with ⟨o, ho⟩ | ⟨r, hr⟩
  · rw [ho]; simp only [Run.Res.bind]; cases o <;> simp [optOr, Run.pure, Run.stop]
  · rw [hr]; exact .inr ⟨r, rfl⟩

open Engine.Accel.ListUpdate in
theorem addCsIn_eq (a : Nat) (cs : Engine.Model.CharSet) (sq : F.Seq F.Math) (s : State F)
    (h : s.heap[a]? = some (.charSet cs)) :
    addCsIn a sq s = (writeCell a (.charSet (F.csAdd cs sq)) >>= fun _ => return .enum Known.eUnused) s := by
  unfold addCsIn take
  simp [h, writeCell, bind, Run.bind, Run.Res.bind, pure, Run.pure]

/-- A List's cell read: the state is unchanged and holds the List at the address. -/
theorem listCell_ok {l : Val F} {s t : State F} {a : Nat} {xs : Array (Val F)}
    (h : Prims.Lists.listCell l s = .ok (a, xs) t) : t = s ∧ ∃ o, s.heap[a]? = some (.list xs o) := by
  unfold Prims.Lists.listCell at h
  split at h
  · rename_i b
    simp only [bind, Run.bind, Ecma.readCell] at h
    cases hb : s.heap[b]? with
    | none => simp [hb, Run.Res.bind] at h
    | some c =>
      rw [hb] at h
      cases c <;> simp [Run.Res.bind, Run.pure, Run.stop] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨rfl, _, hb⟩
  · simp [Run.stop] at h

open Engine.Accel.ListUpdate in
theorem addIn_eq (e l : Val F) : addIn e l = Prims.Lists.setAdd [e, l] := by
  funext s
  cases l <;> try rfl
  rename_i a
  simp only [addIn, Prims.Lists.setAdd, bind, Run.bind, Ecma.readCell, discard]
  cases ha : s.heap[a]? with
  | none => simp [Run.Res.bind]
  | some cell =>
    cases cell with
    | list xs o =>
      simp only [Run.Res.bind]
      rcases Reads.hasElem e xs s with ⟨b, hb⟩ | ⟨r, hb⟩
      · simp only [Run.bind, hb, Run.Res.bind]
        cases b
        · simp [Run.Res.bind, modifyIn_eq, ha, writeList, Run.bind, pure, Run.pure, Functor.mapConst]
        · rfl
      · simp only [Run.bind, hb, Run.Res.bind]
    | charSet cs =>
      simp only [Run.Res.bind]
      rcases Reads.elemSeq e s with ⟨sq, hsq⟩ | ⟨r, hr⟩
      · simp only [Run.bind, hsq, Run.Res.bind]
        rw [addCsIn_eq a cs sq s ha]
        rfl
      · simp only [Run.bind, hr, Run.Res.bind]
    | record _ _ | block _ | env _ _ _ | object _ _ => simp [Run.Res.bind]

open Engine.Accel.ListUpdate in
theorem replaceIn_eq (l old new : Val F) : replaceIn l old new = Prims.Lists.replaceElem [l, old, new] := by
  funext s
  simp only [replaceIn, Prims.Lists.replaceElem, bind, Run.bind]
  cases h : Prims.Lists.listCell l s with
  | esc => rfl
  | stop => rfl
  | ok p t =>
    obtain ⟨a, xs⟩ := p
    obtain ⟨rfl, o, ho⟩ := listCell_ok h
    simp only [Run.Res.bind]
    cases Prims.Lists.indexOf old xs with
    | none => rfl
    | some i => simp [optOr, Run.Res.bind, modifyIn_eq, ho, writeList, Run.bind, pure, Run.pure]

/-- Each entry of the List updates in place is the specification's primitive. -/
theorem listUpdate_eq (q : PrimId) (xs : List (Val F)) (r : Run F (Val F))
    (h : Engine.Accel.ListUpdate.prim q xs = some r) :
    r = Ecma.prim q xs ∧
      (q = Known.pAppend ∨ q = Known.pPrepend ∨ q = Known.pSetAdd ∨ q = Known.pReplaceElem) := by
  unfold Engine.Accel.ListUpdate.prim at h
  split at h
  · rename_i hq
    have hq : q = Known.pAppend := by simpa using hq
    subst hq
    split at h
    · rename_i x a hx
      cases h
      exact ⟨by rw [prim_used _ _ rfl, hx, appendIn_eq], .inl rfl⟩
    · cases h
  split at h
  · rename_i hq
    have hq : q = Known.pPrepend := by simpa using hq
    subst hq
    split at h
    · rename_i x a hx
      cases h
      exact ⟨by rw [prim_used _ _ rfl, hx, prependIn_eq], .inr (.inl rfl)⟩
    · cases h
  split at h
  · rename_i hq
    have hq : q = Known.pSetAdd := by simpa using hq
    subst hq
    split at h
    · rename_i e l hx
      cases h
      exact ⟨by rw [prim_used _ _ rfl, hx, addIn_eq, primOn_setAdd], .inr (.inr (.inl rfl))⟩
    · cases h
  split at h
  · rename_i hq
    have hq : q = Known.pReplaceElem := by simpa using hq
    subst hq
    split at h
    · rename_i l old new hx
      cases h
      exact ⟨by rw [prim_used _ _ rfl, hx, replaceIn_eq, primOn_replaceElem], .inr (.inr (.inr rfl))⟩
    · cases h
  · cases h

/-- The engine's transition at a List update in place is the machine's. -/
theorem listUpdate_step (X : Ctx F) (c : Cfg F) (q : PrimId) (xs : List (Val F)) (r : Run F (Val F))
    (hc : c.ctl = .invoke (.prim q xs)) (h : Engine.Accel.ListUpdate.prim q xs = some r) :
    leafV c r = step X c := by
  obtain ⟨rfl, hq⟩ := listUpdate_eq q xs r h
  exact (step_prim X c q xs hc hq).symm

end Engine.Machine
