module

public import Engine.Host.Core
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas

@[expose] public section

/-!
# `pickJobFast` is `pickJob`
-/

namespace Engine.Host

open Ecma Engine

variable (N : Names)

/-- The first job HostEnqueueGenericJob or HostEnqueuePromiseJob scheduled that the host may take
(`own`) and has not been taken, else the first such timeout job: what `pickJobFast` computes
(`pickJobFast_eq`). -/
def pickJob (log : List (HostCall Impl)) (own : Nat → Bool) : Option Nat :=
  let ks := List.range log.length
  (ks.find? (free N log own [genericJob, promiseJob])).orElse fun _ => ks.find? (free N log own [timeoutJob])

/-- `takeStep` adds the position a call takes. -/
theorem takeStep_has (t : Taken) (e : HostCall Impl) (k : Nat) :
    (takeStep t e).has k = (t.has k || e.takes k) := by
  cases e with
  | next a =>
    cases a with
    | some j =>
      simp only [takeStep, Taken.has, Std.HashSet.contains_insert, HostCall.takes]
      cases (j == k) <;> cases t.1.contains k <;> simp
    | none => simp [takeStep, HostCall.takes]
  | choice q vs r =>
    cases r with
    | math j =>
      simp only [takeStep, HostCall.takes]
      cases (q == Known.pAgentNextJob) <;> simp [Taken.has, Bool.or_left_comm, Bool.or_comm]
    | _ => simp [takeStep, HostCall.takes]
  | _ => simp [takeStep, HostCall.takes]

/-- A fold of `takeStep` adds the positions the log's calls take. -/
theorem takenSet_foldl (log : List (HostCall Impl)) (t : Taken) (k : Nat) :
    (log.foldl takeStep t).has k = (t.has k || log.any (·.takes k)) := by
  induction log generalizing t with
  | nil => simp
  | cons e es ih => rw [List.foldl_cons, ih, List.any_cons, takeStep_has, Bool.or_assoc]

/-- `takenSet` holds the taken positions. -/
theorem takenSet_has (log : List (HostCall Impl)) (k : Nat) :
    (takenSet log).has k = log.any (·.takes k) := by
  rw [takenSet, takenSet_foldl]; simp [Taken.has]

/-- `firstFree` over `es` from position `pre.length` is the first such position of `pre ++ es`. -/
theorem firstFree_eq (t : Taken) (own : Nat → Bool) (secs : List String) :
    ∀ (es pre : List (HostCall Impl)), firstFree N t own secs pre.length es =
      (List.range' pre.length es.length).find? fun k =>
        ((pre ++ es)[k]?.any fun e => secs.any (N.callOf · e)) && own k && !t.has k
  | [], _ => rfl
  | e :: es, pre => by
    have ih := firstFree_eq t own secs es (pre ++ [e])
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at ih
    simp only [firstFree, List.length_cons, List.range'_succ, List.find?_cons, ih,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.any_some]
    cases (secs.any (N.callOf · e) && own pre.length && !t.has pre.length) <;> rfl

/-- `pickJobFast` is `pickJob`. -/
theorem pickJobFast_eq (own : Nat → Bool) (log : List (HostCall Impl)) :
    pickJobFast N own log = pickJob N log own := by
  have h := fun secs => firstFree_eq N (takenSet log) own secs log.reverse []
  simp only [List.length_nil, List.nil_append, List.length_reverse] at h
  simp only [pickJobFast, pickJob, h, ← List.range_eq_range', takenSet_has]
  rfl

end Engine.Host
