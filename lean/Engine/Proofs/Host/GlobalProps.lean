module

public import Engine.Proofs.Host.Host
public import Engine.Proofs.Host.LawsFrame
public import Engine.Proofs.Laws

@[expose] public section

/-!
# HostGlobalProperties keeps the Agent Record

`globalProps_recKeeps`: the Impl host's HostGlobalProperties writes only the global object, so it keeps
the agent and each Record cell (`RecKeeps`).
-/

namespace Engine.SpecHost

open Ecma Engine

theorem fast_allocKeeps : AllocKeeps Impl := fun _ _ _ _ h => heapGet_alloc h

theorem objectOf_keeps (v : Val Impl) : KeepsR (Engine.Host.objectOf v) := by
  unfold Engine.Host.objectOf; keeps_tac

theorem dataProp_keeps (v : Val Impl) (w e c : Bool) : KeepsR (Engine.Host.dataProp v w e c) := by
  have hA := fast_allocKeeps
  unfold Engine.Host.dataProp; keeps_tac

theorem ownValue_keeps (o : Val Impl) (k : String) : KeepsR (Engine.Host.ownValue o k) := by
  unfold Engine.Host.ownValue
  refine KeepsR.bind (objectOf_keeps _) fun _ => ?_
  unfold Ecma.readField Ecma.optOr; keeps_tac

theorem builtinLike_keeps (f : Val Impl) (b : AlgId) (n : String) (l : Nat) :
    KeepsR (Engine.Host.builtinLike f b n l) := by
  have hA := fast_allocKeeps
  unfold Engine.Host.builtinLike
  refine KeepsR.bind (objectOf_keeps _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  keeps_tac

theorem htmlDDA_keeps (d : FieldId) (f : Val Impl) : KeepsR (Engine.Host.htmlDDA d f) := by
  have hA := fast_allocKeeps
  unfold Engine.Host.htmlDDA
  refine KeepsR.bind (objectOf_keeps _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  keeps_tac

theorem ddaProps_keeps (dda : Option FieldId) (f : Val Impl) (ps : Impl.Props (Val Impl)) :
    KeepsR (Engine.Host.ddaProps dda f ps) := by
  unfold Engine.Host.ddaProps
  split
  · refine KeepsR.bind (htmlDDA_keeps _ _) fun _ => ?_
    refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
    exact KeepsR.pure' _
  · exact KeepsR.pure _

theorem memberProps_keeps (f : Val Impl) :
    ∀ (ps : Impl.Props (Val Impl)) (ms : List (AlgId × String × Nat)), KeepsR (Engine.Host.memberProps f ps ms)
  | _, [] => KeepsR.pure _
  | _, (_, _, _) :: ms =>
    KeepsR.bind (builtinLike_keeps _ _ _ _) fun _ =>
    KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => memberProps_keeps f _ ms

theorem agentObject_keeps (f : Val Impl) (sl : Impl.Rec (Val Impl)) : KeepsR (Engine.Host.agentObject f sl) := by
  unfold Engine.Host.agentObject
  refine KeepsR.bind KeepsR.get fun _ => ?_
  refine KeepsR.bind (memberProps_keeps _ _ _) fun _ => ?_
  refine KeepsR.bind (KeepsR.alloc fast_allocKeeps _) fun _ => ?_
  exact KeepsR.pure' _

theorem newGlobals_keeps (dda : Option FieldId) (g : Val Impl) : KeepsR (Engine.Host.newGlobals dda g) := by
  unfold Engine.Host.newGlobals
  refine KeepsR.bind (ownValue_keeps _ _) fun _ => ?_
  refine KeepsR.bind (builtinLike_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (builtinLike_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (builtinLike_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (builtinLike_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (ownValue_keeps _ _) fun _ => ?_
  refine KeepsR.bind (objectOf_keeps _) fun p => ?_
  obtain ⟨_, _⟩ := p
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (agentObject_keeps _ _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (ddaProps_keeps _ _ _) fun _ => ?_
  refine KeepsR.bind (KeepsR.alloc fast_allocKeeps _) fun _ => ?_
  refine KeepsR.bind (builtinLike_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  refine KeepsR.bind (dataProp_keeps _ _ _ _) fun _ => ?_
  exact KeepsR.pure' _

/-- A key `ps` has keeps its property under `putNew`. -/
theorem putNew_get {ps : Impl.Props (Val Impl)} {k : Impl.Str ⊕ Impl.Sym} (h : (Impl.propsGet ps k).isSome)
    (n : String) (v : Val Impl) : Impl.propsGet (Engine.Host.putNew ps n v) k = Impl.propsGet ps k := by
  unfold Engine.Host.putNew
  split
  · rfl
  · rename_i hn
    have hne : k ≠ Engine.Host.keyOf n := fun e => by subst e; simp_all
    exact _root_.Engine.Impl.laws.propsGet_put_other ps _ _ _ hne

/-- An extensible object that only gains properties by `putNew` keeps to the invariants. -/
theorem objKept_putNew {s s' : State Impl}
    (hk : ∀ a t fs, Impl.heapGet s.heap a = some (.record t fs) → Impl.heapGet s'.heap a = some (.record t fs))
    {sl : Impl.Rec (Val Impl)} {ps : Impl.Props (Val Impl)} (hx : Impl.recGet sl Known.fExtensible = some (.bool true))
    (pp po pt : Val Impl) :
    objKept s s' sl ps sl (Engine.Host.putNew (Engine.Host.putNew (Engine.Host.putNew ps "print" pp) "$262" po) "setTimeout" pt) := by
  refine ⟨.inl rfl, fun h => absurd hx h, fun k fs h _ => ⟨fs, ?_, attrsKept_refl fs⟩⟩
  have hs : (Impl.propsGet ps k).isSome := by
    unfold attrsAt at h; split at h
    · rename_i hp; rw [hp]; rfl
    · cases h
  have e : Impl.propsGet (Engine.Host.putNew (Engine.Host.putNew (Engine.Host.putNew ps "print" pp) "$262" po)
      "setTimeout" pt) k = Impl.propsGet ps k := by
    have h1 := putNew_get hs "print" pp
    have hs1 : (Impl.propsGet (Engine.Host.putNew ps "print" pp) k).isSome := by rw [h1]; exact hs
    have h2 := putNew_get hs1 "$262" po
    have hs2 : (Impl.propsGet (Engine.Host.putNew (Engine.Host.putNew ps "print" pp) "$262" po) k).isSome := by
      rw [h2]; exact hs1
    rw [putNew_get hs2, h2, h1]
  have h' := attrsAt_keepsRec hk h
  unfold attrsAt at h' ⊢
  rw [e]
  exact h'

/-- HostGlobalProperties keeps the agent and every Record cell, and every object to the invariants. -/
theorem globalProps_stepKeeps {dda : Option FieldId} {vs : List (Val Impl)} {s : State Impl} {r : Val Impl}
    {s' : State Impl} (h : Run.boundary (Engine.Host.globalProps dda vs) s = .ok r s') : StepKeeps s s' := by
  change Run.Res.boundary (Engine.Host.globalProps dda vs s) = _ at h
  unfold Engine.Host.globalProps at h
  split at h
  · rename_i g
    change Run.Res.boundary (Run.Res.bind (Engine.Host.newGlobals dda (.obj g) s) _) = _ at h
    have hk := newGlobals_keeps dda (.obj g) s
    cases e : Engine.Host.newGlobals dda (.obj g) s with
    | ok x s₁ =>
      rw [e] at h hk
      obtain ⟨pp, po, pt⟩ := x
      change Run.Res.boundary (Run.Res.bind (Engine.Host.objectOf (.obj g) s₁) _) = _ at h
      have hk2 := objectOf_keeps (.obj g) s₁
      cases e2 : Engine.Host.objectOf (.obj g) s₁ with
      | ok y s₂ =>
        rw [e2] at h
        obtain ⟨sl, ps⟩ := y
        obtain ⟨rfl, hg⟩ := objectOf_ok e2
        by_cases hx : Engine.Host.extensibleIn sl = true
        · replace hx' : Impl.recGet sl Known.fExtensible = some (.bool true) := by
            revert hx; unfold Engine.Host.extensibleIn; split <;> simp_all
          simp only [hx, ↓reduceIte, Run.Res.bind, Ecma.writeCell, Bind.bind, Run.bind, Pure.pure, Run.pure,
            Run.Res.boundary, Res.ok.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have hne : ∀ q c, Impl.heapGet s₂.heap q = some c → (∀ sl ps, c ≠ .object sl ps) → g ≠ q :=
            fun q c hq hc e => by subst e; rw [hg] at hq; cases hq; exact hc _ _ rfl
          have hset : ∀ q, g ≠ q → Impl.heapGet (s₂.heap.setIfInBounds g (.object sl
              (Engine.Host.putNew (Engine.Host.putNew (Engine.Host.putNew ps "print" pp) "$262" po) "setTimeout" pt))) q =
              Impl.heapGet s₂.heap q := fun q hq => by
            simp only [Impl, Impl]; rw [Array.getElem?_setIfInBounds_ne hq]
          have hrec : ∀ q k fs, Impl.heapGet s.heap q = some (.record k fs) →
              Impl.heapGet (s₂.heap.setIfInBounds g (.object sl
                (Engine.Host.putNew (Engine.Host.putNew (Engine.Host.putNew ps "print" pp) "$262" po) "setTimeout" pt))) q =
                some (.record k fs) := fun q k fs hq => by
            have hq₁ := hk.2 q _ hq
            rw [hset q (hne q _ hq₁ fun _ _ e => by cases e)]; exact hq₁
          refine ⟨⟨by rw [hk.1], hrec⟩, fun a sl₀ ps₀ ha => ?_⟩
          have ha₁ := hk.2 a _ ha
          by_cases hag : g = a
          · subst hag
            rw [hg] at ha₁; cases ha₁
            refine ⟨sl, _, ?_, objKept_putNew hrec hx' pp po pt⟩
            simp only [Impl, Impl]
            exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hg).1
          · exact ⟨sl₀, ps₀, by rw [hset a hag]; exact ha₁, objKept_keepsRec hrec sl₀ ps₀⟩
        · simp only [hx, Bool.false_eq_true, ↓reduceIte, Run.Res.bind, Bind.bind, Run.bind, Pure.pure, Run.pure,
            Run.Res.boundary, Res.ok.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact hk.stepKeeps
      | esc c s₂ =>
        rw [e2] at h hk2
        simp only [Run.Res.bind, Run.Res.boundary, Res.ok.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact (hk.trans hk2).stepKeeps
      | _ => rw [e2] at h; cases h
    | esc c s₁ =>
      rw [e] at h hk
      simp only [Run.Res.bind, Run.Res.boundary, Res.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hk.stepKeeps
    | _ => rw [e] at h; cases h
  · cases h

end Engine.SpecHost
