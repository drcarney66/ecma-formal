module

@[expose] public section

/-!
# A sound Boolean equality test

`EqB α`: a test `eqB : α → α → Bool` that holds of equal values only (`sound`). Only soundness is stated, never
completeness: the test serves to turn a runtime equality check into an equation (`Engine.Pins.pin`), where the type has
no `DecidableEq` (the specification's syntax: nested and mutual inductive types, whose `DecidableEq` Lean does
not derive). `Engine.Proofs.Pins.Gen.Eq` holds the instances for the specification's types.
-/

namespace Engine.Pins

/-- A Boolean test that holds of equal values only. -/
class EqB (α : Type) where
  eqB : α → α → Bool
  sound : ∀ a b : α, eqB a b = true → a = b

/-- A type with decidable equality: the decision. -/
instance (priority := low) EqB.ofDecidableEq {α : Type} [DecidableEq α] : EqB α where
  eqB a b := decide (a = b)
  sound _ _ h := of_decide_eq_true h

/-- Two lists, element by element. -/
def listEqB {α : Type} [EqB α] : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => EqB.eqB a b && listEqB as bs
  | _, _ => false

theorem listEqB_sound {α : Type} [EqB α] : ∀ a b : List α, listEqB a b = true → a = b
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [listEqB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have e1 := EqB.sound _ _ h1
    have e2 := listEqB_sound _ _ h2
    subst e1 e2
    rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [listEqB] at h

instance {α : Type} [EqB α] : EqB (List α) := ⟨listEqB, listEqB_sound⟩

instance {α : Type} [EqB α] : EqB (Option α) where
  eqB
    | none, none => true
    | some a, some b => EqB.eqB a b
    | _, _ => false
  sound
    | none, none, _ => rfl
    | some _, some _, h => by
      have e := EqB.sound _ _ h
      subst e
      rfl
    | none, some _, h | some _, none, h => by simp at h

instance {α β : Type} [EqB α] [EqB β] : EqB (α × β) where
  eqB a b := EqB.eqB a.1 b.1 && EqB.eqB a.2 b.2
  sound
    | (_, _), (_, _), h => by
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have e1 := EqB.sound _ _ h1
      have e2 := EqB.sound _ _ h2
      subst e1 e2
      rfl

instance {α : Type} [EqB α] : EqB (Array α) where
  eqB a b := listEqB a.toList b.toList
  sound
    | ⟨_⟩, ⟨_⟩, h => by
      have e := listEqB_sound _ _ h
      subst e
      rfl

/-- An equation from its test's evaluation (`EqB.sound`). -/
theorem pin {α : Type} [EqB α] {a b : α} (h : EqB.eqB a b = true) : a = b := EqB.sound a b h

end Engine.Pins
