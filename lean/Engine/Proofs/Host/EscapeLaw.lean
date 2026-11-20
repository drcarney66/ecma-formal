module

public import Engine.Host.Core

@[expose] public section

/-!
# EscapePattern's law at Impl

The engine answers EscapePattern by `refEscape` (`Engine.Host.escapeChoice`). Two list inductions over
`patternEscUnits`: it is `Escaped` (`escaped_patternEscUnits`), and it is `bodySafe` in every state of the scan
(`bodySafe_patternEscUnits`); so `refEscape` meets `EscapeOf` and `BodySafe` (`escapeOf_refEscape`,
`bodySafe_refEscape`), and `escapeChoice` meets `Host.WF.escapePattern` (`escapeChoice_law`).
-/

namespace Engine.SpecHost

open Ecma Engine Engine.Host

/-- An Impl String has its code units. -/
theorem unitsAre_toList (x : Impl.Str) : unitsAre (M := Impl) x (x.toList.map UInt16.toNat) := by
  unfold unitsAre
  have e : seqList (M := Impl) (Impl.strUnits x) = x.toList.map fun u => Engine.Model.MathVal.int u.toNat := by
    show Array.foldl _ [] (x.map _) = _
    rw [← Array.foldl_toList, Array.toList_map]
    have : ∀ (acc l : List Engine.Model.MathVal), l.foldl (fun l x => l ++ [x]) acc = acc ++ l := by
      intro acc l
      induction l generalizing acc with
      | nil => simp
      | cons x l ih => simp [ih]
    exact (this [] _).trans (List.nil_append _)
  rw [e]
  generalize x.toList = xs
  induction xs with
  | nil => exact trivial
  | cons u xs ih => exact ⟨show ((u.toNat : Int) == (u.toNat : Int)) = true from beq_self_eq_true _, ih⟩

/-- A code unit other than LF, CR, LS and PS is no LineTerminator. -/
theorem lineTerminatorUnit_false {c : UInt16} (h10 : ¬c = 10) (h13 : ¬c = 13) (h28 : ¬c = 0x2028)
    (h29 : ¬c = 0x2029) : lineTerminatorUnit c.toNat = false := by
  simp only [← UInt16.toNat_inj] at h10 h13 h28 h29
  simp only [lineTerminatorUnit, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  exact ⟨⟨⟨h10, h13⟩, h28⟩, h29⟩

theorem asciiUnits_u2028 : (asciiUnits "u2028").map UInt16.toNat = [117, 50, 48, 50, 56] := by decide
theorem asciiUnits_u2029 : (asciiUnits "u2029").map UInt16.toNat = [117, 50, 48, 50, 57] := by decide
theorem asciiUnits_bu2028 : (asciiUnits "\\u2028").map UInt16.toNat = [92, 117, 50, 48, 50, 56] := by decide
theorem asciiUnits_bu2029 : (asciiUnits "\\u2029").map UInt16.toNat = [92, 117, 50, 48, 50, 57] := by decide
theorem asciiUnits_group : (asciiUnits "(?:)").map UInt16.toNat = [40, 63, 58, 41] := by decide

/-- **`patternEscUnits` escapes**: `b` the unit before an unescaped `\`. -/
theorem escaped_patternEscUnits : ∀ (b : Bool) (p : List UInt16),
    Escaped b (p.map UInt16.toNat) ((patternEscUnits b p).map UInt16.toNat)
  | b, [] => by cases b <;> exact .nil _
  | true, c :: cs => by
    have ih := escaped_patternEscUnits false cs
    simp only [patternEscUnits, List.map_cons, List.map_append]
    by_cases h10 : c = 10
    · subst h10; exact .terminatorAfter (by decide) ih
    by_cases h13 : c = 13
    · subst h13; exact .terminatorAfter (by decide) ih
    by_cases h28 : c = 0x2028
    · subst h28; simp only [↓reduceIte]; exact .terminatorAfter (by decide) ih
    by_cases h29 : c = 0x2029
    · subst h29; simp only [↓reduceIte]; exact .terminatorAfter (by decide) ih
    simp only [h10, h13, h28, h29, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    exact .keep (lineTerminatorUnit_false h10 h13 h28 h29) (by simpa using ih)
  | false, c :: cs => by
    simp only [patternEscUnits]
    by_cases h92 : c = 92
    · subst h92
      exact .keep (by decide) (escaped_patternEscUnits true cs)
    have ih := escaped_patternEscUnits false cs
    simp only [h92, ↓reduceIte, List.map_cons, List.map_append]
    by_cases h47 : c = 47
    · subst h47; exact .slash ih
    by_cases h10 : c = 10
    · subst h10; exact .terminator (by decide) ih
    by_cases h13 : c = 13
    · subst h13; exact .terminator (by decide) ih
    by_cases h28 : c = 0x2028
    · subst h28; simp only [↓reduceIte]; exact .terminator (by decide) ih
    by_cases h29 : c = 0x2029
    · subst h29; simp only [↓reduceIte]; exact .terminator (by decide) ih
    simp only [h47, h10, h13, h28, h29, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append]
    refine .keep (lineTerminatorUnit_false h10 h13 h28 h29) ?_
    have : (c.toNat == 92) = false := by simpa [← UInt16.toNat_inj] using h92
    simpa [this] using ih

/-- **`patternEscUnits` is `bodySafe`**, whatever the class state: it holds no LineTerminator and no `/` but
after an unescaped `\`. -/
theorem bodySafe_patternEscUnits : ∀ (b : Bool) (p : List UInt16) (cls : Bool),
    bodySafe b cls ((patternEscUnits b p).map UInt16.toNat) = true
  | b, [], cls => by cases b <;> rfl
  | true, c :: cs, cls => by
    have ih := bodySafe_patternEscUnits false cs cls
    simp only [patternEscUnits, List.map_append]
    by_cases h10 : c = 10
    · subst h10; simpa [bodySafe, lineTerminatorUnit] using ih
    by_cases h13 : c = 13
    · subst h13; simpa [bodySafe, lineTerminatorUnit] using ih
    by_cases h28 : c = 0x2028
    · subst h28; simpa [bodySafe, lineTerminatorUnit, asciiUnits_u2028] using ih
    by_cases h29 : c = 0x2029
    · subst h29; simpa [bodySafe, lineTerminatorUnit, asciiUnits_u2029] using ih
    simp only [h10, h13, h28, h29, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      bodySafe, lineTerminatorUnit_false h10 h13 h28 h29]
    simp [ih]
  | false, c :: cs, cls => by
    simp only [patternEscUnits]
    by_cases h92 : c = 92
    · subst h92
      simpa [bodySafe, lineTerminatorUnit] using bodySafe_patternEscUnits true cs cls
    simp only [h92, ↓reduceIte, List.map_append]
    by_cases h47 : c = 47
    · subst h47; simpa [bodySafe, lineTerminatorUnit] using bodySafe_patternEscUnits false cs cls
    by_cases h10 : c = 10
    · subst h10; simpa [bodySafe, lineTerminatorUnit] using bodySafe_patternEscUnits false cs cls
    by_cases h13 : c = 13
    · subst h13; simpa [bodySafe, lineTerminatorUnit] using bodySafe_patternEscUnits false cs cls
    by_cases h28 : c = 0x2028
    · subst h28; simpa [bodySafe, lineTerminatorUnit, asciiUnits_bu2028] using bodySafe_patternEscUnits false cs cls
    by_cases h29 : c = 0x2029
    · subst h29; simpa [bodySafe, lineTerminatorUnit, asciiUnits_bu2029] using bodySafe_patternEscUnits false cs cls
    simp only [h47, h10, h13, h28, h29, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, bodySafe, lineTerminatorUnit_false h10 h13 h28 h29]
    have h92' : (c.toNat == 92) = false := by simpa [← UInt16.toNat_inj] using h92
    have h47' : (c.toNat != 47) = true := by simpa [← UInt16.toNat_inj] using h47
    simp [h92', h47', bodySafe_patternEscUnits false cs]

/-- `patternEscUnits` of a non-empty list begins with a unit. -/
theorem patternEscUnits_cons (b : Bool) (c : UInt16) (cs : List UInt16) :
    ∃ d ds, patternEscUnits b (c :: cs) = d :: ds := by
  cases b <;> simp only [patternEscUnits] <;> repeat (first | split | exact ⟨_, _, rfl⟩ | simp only [List.cons_append])
  all_goals simp [asciiUnits]

/-- `refEscape` meets `EscapeOf`. -/
theorem escapeOf_refEscape (p : Impl.Str) :
    EscapeOf (p.toList.map UInt16.toNat) ((refEscape p).toList.map UInt16.toNat) := by
  unfold refEscape EscapeOf
  by_cases h : p.size = 0
  · have : p.toList = [] := by simpa using h
    simp only [h, ↓reduceIte, this, List.map_nil, List.toList_toArray, asciiUnits_group]
    exact .inl ⟨by simp, by simp⟩
  · have : p.toList ≠ [] := by simpa using h
    simp only [h, ↓reduceIte, List.toList_toArray]
    exact .inr ⟨by simpa using this, escaped_patternEscUnits false p.toList⟩

/-- `refEscape` meets `BodySafe`. -/
theorem bodySafe_refEscape (p : Impl.Str) : BodySafe ((refEscape p).toList.map UInt16.toNat) := by
  unfold refEscape BodySafe
  by_cases h : p.size = 0
  · simp only [h, ↓reduceIte, List.toList_toArray, asciiUnits_group]
    decide
  · simp only [h, ↓reduceIte, List.toList_toArray]
    refine ⟨?_, bodySafe_patternEscUnits false p.toList false⟩
    obtain ⟨c, cs, hc⟩ : ∃ c cs, p.toList = c :: cs := by
      cases hp : p.toList with
      | nil => exact absurd (by simpa using hp) h
      | cons c cs => exact ⟨c, cs, rfl⟩
    rw [hc]
    obtain ⟨d, ds, hd⟩ := patternEscUnits_cons false c cs
    rw [hd]
    simp

/-- **EscapePattern's law of `escapeChoice`** (`Host.WF.escapePattern` at a host whose choice it is). -/
theorem escapeChoice_law {pattern flags : Impl.Str} {s s' : State Impl} {r : Val Impl}
    (h : escapeChoice [.str pattern, .str flags] s = .ok r s') :
    s' = s ∧ (∃ S, r = .str S ∧ ∃ p e, unitsAre pattern p ∧ unitsAre S e ∧ EscapeOf p e ∧ BodySafe e) ∧
      ∀ s2 r2 s2', escapeChoice [.str pattern, .str flags] s2 = .ok r2 s2' → r2 = r := by
  simp only [escapeChoice, Run.pure] at h
  cases h
  refine ⟨rfl, ⟨_, rfl, _, _, unitsAre_toList _, unitsAre_toList _, escapeOf_refEscape pattern,
    bodySafe_refEscape pattern⟩, fun s2 r2 s2' h2 => ?_⟩
  simp only [escapeChoice, Run.pure] at h2
  cases h2
  rfl

/-- info: 'Engine.SpecHost.escapeChoice_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms escapeChoice_law

end Engine.SpecHost
