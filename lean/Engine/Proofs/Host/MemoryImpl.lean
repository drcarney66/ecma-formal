module

public import Engine.Proofs.Host.Laws
public import Engine.Proofs.Host.MemorySnoc

@[expose] public section

/-!
# Law L2 for a sequentially consistent ChooseReadsBytesFrom

`scWrites` reads each byte from its latest write in the interleaving order of the log's switches.
Where memory order agrees with that order (`interleaved`), each chosen write is memory-order last
among the writes of its byte, so `snoc_valid` keeps the execution valid with the read appended.
-/

namespace Ecma.MemoryModel

open Ecma

variable {M : Model}

/-! Places in the interleaving order. -/

theorem placeLe_refl (p : Nat × Nat) : placeLe p p = true := by
  simp [placeLe]

theorem placeLe_total (p q : Nat × Nat) : placeLe p q = true ∨ placeLe q p = true := by
  simp only [placeLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; omega

theorem placeLe_trans {p q r : Nat × Nat} (h₁ : placeLe p q = true) (h₂ : placeLe q r = true) :
    placeLe p r = true := by
  simp only [placeLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *; omega

/-- The latest write of byte `loc` is placed no earlier than any placed write of it. -/
theorem lastWrite_max {isWrite : State M → Val M → Bool} {s : State M} {block : Val M} {loc : M.Math}
    {es : List (Val M × (Nat × Nat))} {q : Val M × (Nat × Nat)} (h : Ecma.lastWrite isWrite s block loc es = some q) :
    ∀ ep ∈ es, writesByte isWrite s block loc ep.1 = true → placeLe ep.2 q.2 = true := by
  let g := fun (acc : Option (Val M × (Nat × Nat))) (ep : Val M × (Nat × Nat)) =>
    if writesByte isWrite s block loc ep.1 then
      match acc with
      | some q => if placeLe q.2 ep.2 then some ep else acc
      | none => some ep
    else acc
  have key : ∀ (l : List (Val M × (Nat × Nat))) (acc : Option (Val M × (Nat × Nat)))
      (S : Val M × (Nat × Nat) → Prop),
      (∀ ep, S ep → writesByte isWrite s block loc ep.1 = true → ∃ q, acc = some q ∧ placeLe ep.2 q.2 = true) →
      ∀ ep, (S ep ∨ ep ∈ l) → writesByte isWrite s block loc ep.1 = true →
        ∃ q, l.foldl g acc = some q ∧ placeLe ep.2 q.2 = true := by
    intro l
    induction l with
    | nil =>
      intro acc S hS ep hep hw
      rcases hep with h | h
      · exact hS ep h hw
      · simp at h
    | cons x l ih =>
      intro acc S hS ep hep hw
      simp only [List.foldl_cons]
      refine ih (g acc x) (fun e => S e ∨ e = x) ?_ ep ?_ hw
      · intro e he hwe
        rcases he with he | rfl
        · obtain ⟨q, rfl, hle⟩ := hS e he hwe
          by_cases hx : writesByte isWrite s block loc x.1 = true
          · by_cases hqx : placeLe q.2 x.2 = true
            · exact ⟨x, by simp [g, hx, hqx], placeLe_trans hle hqx⟩
            · exact ⟨q, by simp [g, hx, hqx], hle⟩
          · exact ⟨q, by simp [g, hx], hle⟩
        · cases acc with
          | none => exact ⟨e, by simp [g, hwe], placeLe_refl _⟩
          | some q =>
            by_cases hqx : placeLe q.2 e.2 = true
            · exact ⟨e, by simp [g, hwe, hqx], placeLe_refl _⟩
            · exact ⟨q, by simp [g, hwe, hqx], (placeLe_total _ _).resolve_left hqx⟩
      · rcases hep with h | h
        · exact .inl (.inl h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inl (.inr rfl)
          · exact .inr h
  intro ep hep hw
  obtain ⟨q', hq', hle⟩ := key es none (fun _ => False) (fun _ h => h.elim) ep (.inr hep) hw
  have e : Ecma.lastWrite isWrite s block loc es = es.foldl g none := rfl
  rw [e, hq'] at h
  cases h
  exact hle

/-- An event of a List is placed. -/
theorem placed_of_mem {f : Nat → Nat × Nat} {w : Val M} :
    ∀ {i : Nat} {es : List (Val M)}, w ∈ es → ∃ p, (w, p) ∈ placed f i es
  | _, [], h => by simp at h
  | i, _ :: _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨f i, by simp [placed]⟩
    · obtain ⟨p, hp⟩ := placed_of_mem (f := f) (i := i + 1) h
      exact ⟨p, by simp [placed, hp]⟩

/-! The view through `memNames`. -/

theorem idxOf?_toList {α : Type} [BEq α] (xs : Array α) (a : α) : xs.idxOf? a = xs.toList.idxOf? a := by
  conv => lhs; rw [← Array.toArray_toList (xs := xs)]
  rw [List.idxOf?_toArray]

theorem fieldIdsL : ["EventsRecords", "EventList", "Block", "ByteIndex", "ElementSize"].map (Gen.fields.toList.idxOf? ·) =
    [some Known.fEventsRecords, some Known.fEventList, some Known.fBlock, some Known.fByteIndex, some Known.fElementSize] := by
  decide +kernel

theorem fieldIds : memNames.field? "EventsRecords" = some Known.fEventsRecords ∧
    memNames.field? "EventList" = some Known.fEventList ∧ memNames.field? "Block" = some Known.fBlock ∧
    memNames.field? "ByteIndex" = some Known.fByteIndex ∧ memNames.field? "ElementSize" = some Known.fElementSize := by
  have h := fieldIdsL
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  simp only [memNames, idxOf?_toList]
  exact h

theorem sortIdsL : ["WriteSharedMemory", "ReadModifyWriteSharedMemory", "ReadSharedMemory"].map (Gen.sorts.toList.idxOf? ·) =
    [some 35, some 150, some 37] := by
  decide +kernel

theorem sortIds : memNames.sort? "WriteSharedMemory" = some 35 ∧
    memNames.sort? "ReadModifyWriteSharedMemory" = some 150 ∧ memNames.sort? "ReadSharedMemory" ≠ some 35 ∧
    memNames.sort? "ReadSharedMemory" ≠ some 150 ∧ memNames.sort? "WriteSharedMemory" ≠ some 150 := by
  have h := sortIdsL
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  simp only [memNames, idxOf?_toList]
  obtain ⟨h₁, h₂, h₃⟩ := h
  simp [h₁, h₂, h₃]

theorem noSuper : Gen.sortDefs.toList.all (fun o => !((o.map SortDef.super).getD []).contains 35) = true ∧
    Gen.sortDefs.toList.all (fun o => !((o.map SortDef.super).getD []).contains 150) = true := by
  decide +kernel

theorem noSuper_at {t : SortId}
    (h : Gen.sortDefs.toList.all (fun o => !((o.map SortDef.super).getD []).contains t) = true) (k : SortId) :
    (((Gen.sortDefs[k]?).join.map SortDef.super).getD []).contains t = false := by
  rcases hk : Gen.sortDefs[k]? with _ | o
  · simp
  · obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hk
    have hm : o ∈ Gen.sortDefs.toList := Array.mem_toList_iff.mpr (heq ▸ Array.getElem_mem hlt)
    have := List.all_eq_true.mp h o hm
    simpa using this

theorem dataSubSort_refl (f : Nat) (k : SortId) : dataSubSort f k k = true := by
  cases f <;> simp [dataSubSort]

/-- A sort no sort lists as its super has no subsort but itself. -/
theorem dataSubSort_eq {t : SortId}
    (hns : ∀ k : SortId, (((Gen.sortDefs[k]?).join.map SortDef.super).getD []).contains t = false) :
    ∀ f k, dataSubSort f k t = true → k = t
  | 0, k, h => by simpa [dataSubSort] using h
  | f + 1, k, h => by
    simp only [dataSubSort, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h with h | ⟨j, hj, hd⟩
    · exact h
    · obtain rfl := dataSubSort_eq hns f j hd
      have := hns k
      simp [hj] at this

theorem field_eq {s : State M} {v : Val M} {n : String} {f : FieldId} (h : memNames.field? n = some f) :
    View.field memNames s v n = (fieldOf s f v).getD .absent := by
  cases v with
  | ref a =>
    simp only [View.field, View.cell, fieldOf, h]
    rcases M.heapGet s.heap a with _ | c
    · rfl
    · cases c <;> rfl
  | _ => simp [View.field, View.cell, fieldOf]

theorem list_field {s : State M} {v : Val M} {n : String} {f : FieldId} (h : memNames.field? n = some f) :
    View.list s (View.field memNames s v n) = fieldElems s f v := by
  rw [field_eq h]
  simp only [fieldElems]
  rcases fieldOf s f v with _ | w
  · rfl
  · cases w with
    | ref a =>
      simp only [Option.getD_some, Option.bind_some, View.list, View.cell, listElems]
      rcases M.heapGet s.heap a with _ | c
      · rfl
      · cases c <;> rfl
    | _ => rfl

theorem addr_eq_some {v : Val M} {a : M.Addr} : View.addr v = some a ↔ v = .ref a := by
  cases v <;> simp [View.addr]

/-- An event of the view is one of an [[EventList]] of its [[EventsRecords]]. -/
theorem inEvents_iff {d : CloSite → List (Val M) → List (Val M) → Run M (Val M)} {s : State M} {ex : Val M} {a : M.Addr} :
    inEvents (View.exec memNames d s ex) a ↔
      ∃ er ∈ fieldElems s Known.fEventsRecords ex, .ref a ∈ fieldElems s Known.fEventList er := by
  have hr : (View.exec memNames d s ex).records = (fieldElems s Known.fEventsRecords ex).map (View.eventsRecord memNames s) := by
    simp only [View.exec, list_field fieldIds.1]
  have he : ∀ er, (View.eventsRecord memNames s er).events = (fieldElems s Known.fEventList er).filterMap View.addr :=
    fun er => by simp only [View.eventsRecord, list_field fieldIds.2.1]
  rw [inEvents, hr]
  constructor
  · rintro ⟨_, hm, ha⟩
    obtain ⟨er, her, rfl⟩ := List.mem_map.mp hm
    rw [he] at ha
    obtain ⟨v, hv, hva⟩ := List.mem_filterMap.mp ha
    rw [addr_eq_some] at hva
    subst hva
    exact ⟨er, her, hv⟩
  · rintro ⟨er, her, hv⟩
    exact ⟨_, List.mem_map.mpr ⟨er, her, rfl⟩, by rw [he]; exact List.mem_filterMap.mpr ⟨_, hv, rfl⟩⟩

theorem inEvents_of_placed {d : CloSite → List (Val M) → List (Val M) → Run M (Val M)} {s : State M} {ex : Val M} {a : M.Addr} {p : Nat × Nat}
    (h : (.ref a, p) ∈ placedEvents s (cutsOf s.hostLog) ex) : inEvents (View.exec memNames d s ex) a := by
  have := mem_placedEvents h
  simp only [execEvents, List.mem_flatMap] at this
  exact inEvents_iff.mpr this

theorem placed_of_inEvents {d : CloSite → List (Val M) → List (Val M) → Run M (Val M)} {s : State M} {ex : Val M} {a : M.Addr}
    (h : inEvents (View.exec memNames d s ex) a) : ∃ p, (.ref a, p) ∈ placedEvents s (cutsOf s.hostLog) ex := by
  obtain ⟨er, her, hv⟩ := inEvents_iff.mp h
  obtain ⟨p, hp⟩ := placed_of_mem (f := eventPlace s (cutsOf s.hostLog) ((fieldOf s Known.fAgentSignifier er).getD .absent))
    (i := 0) hv
  exact ⟨p, List.mem_flatMap.mpr ⟨er, her, hp⟩⟩

/-- A write event of the view is a WriteSharedMemory or ReadModifyWriteSharedMemory Record. -/
theorem isWrite_iff {d : CloSite → List (Val M) → List (Val M) → Run M (Val M)} {s : State M} {ex : Val M} {a : M.Addr} :
    isWrite (View.exec memNames d s ex) a ↔ isWriteEvent s (.ref a) = true := by
  obtain ⟨hW, hRMW, hR35, hR150, hW150⟩ := sortIds
  simp only [memNames] at hW hRMW hR35 hR150 hW150
  simp only [isWrite, View.exec, View.kind, isWriteEvent, isRecordOf, memNames, hW, hRMW]
  rcases M.heapGet s.heap a with _ | c
  · simp
  · cases c
    case record k fs =>
      simp only [Bool.or_eq_true]
      constructor
      · intro h
        by_cases h35 : k = 35
        · subst h35; simp [dataSubSort_refl]
        · by_cases h150 : k = 150
          · subst h150; simp [dataSubSort_refl]
          · exfalso
            simp only [beq_iff_eq, Option.some.injEq, show ¬ (35 = k) from fun e => h35 e.symm,
              show ¬ (150 = k) from fun e => h150 e.symm, if_false] at h
            revert h
            repeat' split
            all_goals simp
      · intro h
        rcases h with h | h
        · obtain rfl := dataSubSort_eq (noSuper_at noSuper.1) 64 k h; simp [hR35]
        · obtain rfl := dataSubSort_eq (noSuper_at noSuper.2) 64 k h; simp [hR150]
    all_goals simp

theorem isRef_of_isWriteEvent {s : State M} {w : Val M} (h : isWriteEvent s w = true) : ∃ a, w = .ref a := by
  cases w with
  | ref a => exact ⟨a, rfl⟩
  | _ => simp [isWriteEvent, isRecordOf] at h

theorem fieldOf_math {s : State M} {f : FieldId} {v : Val M} {i : M.Math} :
    mathField s f v = some i ↔ fieldOf s f v = some (.math i) := by
  simp only [mathField]; split <;> simp_all

/-- A write of byte `loc` of block `b` as `writesByte` sees it. -/
theorem writesByte_iff (hE : ∀ a b : M.Addr, M.addrEq a b = true ↔ a = b) {s : State M} {b a : M.Addr} {loc : M.Math} :
    writesByte isWriteEvent s (.ref b) loc (.ref a) = true ↔ isWriteEvent s (.ref a) = true ∧
      fieldOf s Known.fBlock (.ref a) = some (.ref b) ∧ ∃ i k, fieldOf s Known.fByteIndex (.ref a) = some (.math i) ∧
        fieldOf s Known.fElementSize (.ref a) = some (.math k) ∧ M.lt loc i = false ∧ M.lt loc (M.add i k) = true := by
  have hsame : ∀ v : Val M, Val.same v (.ref b) = true ↔ v = .ref b := fun v => by
    cases v <;> simp [Val.same, hE]
  simp only [writesByte, Bool.and_eq_true, Option.any_eq_true, hsame, exists_eq_right]
  constructor
  · rintro ⟨⟨hw, hb⟩, hr⟩
    refine ⟨hw, hb, ?_⟩
    split at hr
    · rename_i i k hi hk
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hr
      exact ⟨i, k, fieldOf_math.mp hi, fieldOf_math.mp hk, hr⟩
    · cases hr
  · rintro ⟨hw, hb, i, k, hi, hk, h₁, h₂⟩
    refine ⟨⟨hw, hb⟩, ?_⟩
    rw [fieldOf_math.mpr hi, fieldOf_math.mpr hk]
    simp [h₁, h₂]

/-- ChooseReadsBytesFrom, sequentially consistent: law L2, where memory order agrees with the
interleaving order. -/
theorem scWrites_valid (F : IntFacts M) (hE : ∀ a b : M.Addr, M.addrEq a b = true ↔ a = b)
    {vs : List (Val M)} {s : State M} {r : Val M} {s' : State M} (h : scWrites isWriteEvent vs s = .ok r s') :
    ∀ ex er b idx size, vs = [ex, er, .ref b, .math idx, .math size] →
    ∃ ws : List M.Addr, listOf (ws.map .ref) s = .ok r s' ∧
      ∀ (d : CloSite → List (Val M) → List (Val M) → Run M (Val M)) rbf hsw mo k (ev : NewEvent M),
        let x := View.exec memNames d s ex
        ValidWith x rbf hsw → MemoryOrder x rbf hsw mo → interleaved s ex mo →
        View.Formed memNames d s ex → x.records[k]? = some (View.eventsRecord memNames s er) →
        ev.IsRead → ev.block = b → ev.byteIndex = idx → ev.elementSize = size → (∃ m, size = M.ofNat m) →
        ReadsValid x rbf hsw k ev ws := by
  intro ex er b idx size hvs
  subst hvs
  simp only [scWrites, readArgs] at h
  split at h
  · rename_i heq
    split at h
    · rename_i wsv hwsv
      obtain ⟨hl, hk⟩ := eachByte_spec hwsv
      have hq : ∀ j w, wsv[j]? = some w → ∃ p, Ecma.lastWrite isWriteEvent s (.ref b) (M.add idx (M.ofNat j))
          (placedEvents s (cutsOf s.hostLog) ex) = some (w, p) := fun j w hw => by
        have hf := hk j w hw
        rw [Nat.zero_add, Option.map_eq_some_iff] at hf
        obtain ⟨⟨w', p⟩, hq, rfl⟩ := hf
        exact ⟨p, hq⟩
      have hrefs : ∀ w ∈ wsv, ∃ a, w = .ref a := fun w hw => by
        obtain ⟨j, hj⟩ := mem_getElem? hw
        obtain ⟨p, hp⟩ := hq j w hj
        have hwb := (lastWrite_spec hp).2
        simp only [writesByte, Bool.and_eq_true] at hwb
        exact isRef_of_isWriteEvent hwb.1.1
      obtain ⟨ws, rfl⟩ : ∃ ws : List M.Addr, wsv = ws.map .ref := by
        refine ⟨wsv.filterMap View.addr, ?_⟩
        clear hq hk hl hwsv heq h
        induction wsv with
        | nil => rfl
        | cons w wsv ih =>
          obtain ⟨a, rfl⟩ := hrefs w List.mem_cons_self
          simp only [List.filterMap_cons, View.addr, List.map_cons]
          rw [← ih fun w hw => hrefs w (List.mem_cons_of_mem _ hw)]
      refine ⟨ws, h, ?_⟩
      intro d rbf hsw mo k ev x hv hmo hint hform hrec hr hb hidx hsize hsz cv hcv hc
      obtain ⟨n, hn⟩ := hr.byteIndex
      have hloc : ∀ j : Nat, M.add ev.byteIndex (M.ofNat j) = M.ofNat (n + j) := fun j => by
        rw [hn, F.add_ofNat]
      have hq' : ∀ j a, ws[j]? = some a → ∃ p, Ecma.lastWrite isWriteEvent s (.ref b) (M.add idx (M.ofNat j))
          (placedEvents s (cutsOf s.hostLog) ex) = some (.ref a, p) := fun j a hj =>
        hq j (.ref a) (by simp [List.getElem?_map, hj])
      have hf : ∀ e, inSdb x e → FormedAt x e := fun e he => by
        obtain ⟨-, ⟨n, hn⟩, ⟨m, hm⟩⟩ := hform e he
        exact ⟨⟨n, by simp [x, View.exec, hn, View.math]⟩, ⟨m, by simp [x, View.exec, hm, View.math]⟩⟩
      have hws : ∀ (i : Nat) w, ws[i]? = some w → inSdb x w ∧ isWrite x w ∧ x.block w = ev.block ∧
          inRange x w (M.add ev.byteIndex (M.ofNat i)) := fun i a hi => by
        obtain ⟨p, hp⟩ := hq' i a hi
        obtain ⟨hmem, hwb⟩ := lastWrite_spec hp
        rw [writesByte_iff hE] at hwb
        obtain ⟨hw, hblk, bi, es, hbi, hes, h₁, h₂⟩ := hwb
        have hwx : isWrite x a := isWrite_iff.mpr hw
        refine ⟨⟨inEvents_of_placed hmem, .inr hwx⟩, hwx, ?_, ?_⟩
        · simp [x, View.exec, field_eq fieldIds.2.2.1, hblk, View.addr, hb]
        · have ebi : x.byteIndex a = bi := by simp [x, View.exec, field_eq fieldIds.2.2.2.1, hbi, View.math]
          have ees : x.elementSize a = es := by simp [x, View.exec, field_eq fieldIds.2.2.2.2, hes, View.math]
          refine ⟨by rw [hloc]; exact F.isInt_ofNat _, ?_, ?_⟩
          · rw [ebi, hidx]; exact h₁
          · rw [ebi, ees, hidx]; exact h₂
      have hlast : ∀ (i : Nat) w v, ws[i]? = some w → inSdb x v → isWrite x v → x.block v = ev.block →
          inRange x v (M.add ev.byteIndex (M.ofNat i)) → v ≠ w → mo v w := fun i w v hi hv hwv hbv hrv hne => by
        obtain ⟨pw, hp⟩ := hq' i w hi
        obtain ⟨pv, hpv⟩ := placed_of_inEvents hv.1
        obtain ⟨⟨bb, hbb⟩, ⟨n', hn'⟩, ⟨m', hm'⟩⟩ := hform v hv
        rw [field_eq fieldIds.2.2.1] at hbb
        rw [field_eq fieldIds.2.2.2.1] at hn'
        rw [field_eq fieldIds.2.2.2.2] at hm'
        have hfb : fieldOf s Known.fBlock (.ref v) = some (.ref b) := by
          have : x.block v = bb := by simp [x, View.exec, field_eq fieldIds.2.2.1, hbb, View.addr]
          rw [hbv, hb] at this
          rw [← this] at hbb
          rcases e : fieldOf s Known.fBlock (.ref v) with _ | c
          · rw [e] at hbb; cases hbb
          · rw [e] at hbb; simpa using hbb
        have hfi : fieldOf s Known.fByteIndex (.ref v) = some (.math (M.ofNat n')) := by
          rcases e : fieldOf s Known.fByteIndex (.ref v) with _ | c
          · rw [e] at hn'; cases hn'
          · rw [e] at hn'; simpa using hn'
        have hfe : fieldOf s Known.fElementSize (.ref v) = some (.math (M.ofNat m')) := by
          rcases e : fieldOf s Known.fElementSize (.ref v) with _ | c
          · rw [e] at hm'; cases hm'
          · rw [e] at hm'; simpa using hm'
        have ebi : x.byteIndex v = M.ofNat n' := by simp [x, View.exec, field_eq fieldIds.2.2.2.1, hfi, View.math]
        have ees : x.elementSize v = M.ofNat m' := by simp [x, View.exec, field_eq fieldIds.2.2.2.2, hfe, View.math]
        have hwvb : writesByte isWriteEvent s (.ref b) (M.add idx (M.ofNat i)) (.ref v) = true := by
          rw [writesByte_iff hE]
          obtain ⟨-, h₁, h₂⟩ := hrv
          rw [ebi, hidx] at h₁
          rw [ebi, ees, hidx] at h₂
          exact ⟨isWrite_iff.mp hwv, hfb, _, _, hfi, hfe, h₁, h₂⟩
        have hle := lastWrite_max hp (.ref v, pv) hpv hwvb
        exact hint v w pv pw hpv (lastWrite_spec hp).1 hne hle
      have hlen : M.eq (M.ofNat ws.length) ev.elementSize = true := by
        rw [← List.length_map (f := Val.ref), hl, hsize]; exact heq
      have hk' : k < x.records.length := (List.getElem?_eq_some_iff.mp hrec).1
      have hsz' : ∃ m, ev.elementSize = M.ofNat m := by rw [hsize]; exact hsz
      exact (snoc_valid F hv hmo hf hsz' hk' hr hlen hws hlast hc hcv).1
    · cases h
  · cases h

end Ecma.MemoryModel
