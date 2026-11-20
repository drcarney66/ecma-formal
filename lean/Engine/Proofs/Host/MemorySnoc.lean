module

public import Ecma.MemoryModel.Read
public import Ecma.State
public import Engine.Proofs.Host.ObsLaws

@[expose] public section

/-!
# A read last in memory order keeps an execution valid

`snoc_valid`: where `x` is a valid execution with memory order `mo`, its Shared Data Block events'
ranges non-negative integers, a read appended to one of its
Agent Events Records, reading each byte from that byte's memory-order-latest write of its block, is
a valid execution with `mo` and the read last (`Rel.snoc`). The read only adds Relation edges into
itself (`hb_snoc`), so the old events keep their relations.
-/

namespace Ecma.MemoryModel

variable {M : Model} {E : Type} {x : Exec M E} {k : Nat} {r : NewEvent M} {cv : List M.Math}

/-- `mo`, the new event after the events of `x`. -/
def Rel.snoc (x : Exec M E) (mo : Rel E) : Rel (Option E)
  | some a, some b => mo a b
  | some a, none => inEvents x a
  | none, _ => False

/-! The events of `x.snoc k r cv`. -/

theorem snoc_records_get (i : Nat) :
    (x.snoc k r cv).records[i]? = x.records[i]?.map (EventsRecord.snoc k i) := by
  simp [Exec.snoc, List.getElem?_mapIdx]

theorem mem_snoc_records {rec : EventsRecord (Option E)} (h : rec ∈ (x.snoc k r cv).records) :
    ∃ i er, x.records[i]? = some er ∧ rec = EventsRecord.snoc k i er := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  rw [snoc_records_get] at hi
  obtain ⟨er, her, rfl⟩ := Option.map_eq_some_iff.mp hi
  exact ⟨i, er, her, rfl⟩

theorem snoc_tail (k i : Nat) : (if i = k then [none] else []) = ([] : List (Option E)) ∨
    (if i = k then [none] else []) = [(none : Option E)] := by
  split <;> simp

theorem get_snoc_some {evs : List E} {t : List (Option E)} (ht : t = [] ∨ t = [none]) {i : Nat} {a : E}
    (h : (evs.map some ++ t)[i]? = some (some a)) : evs[i]? = some a := by
  by_cases hi : i < evs.length
  · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map] at h
    simpa using h
  · rw [List.getElem?_append_right (by simp; omega)] at h
    rcases ht with rfl | rfl
    · simp at h
    · have : i - (evs.map some).length = 0 := by
        cases e : i - (evs.map some).length with
        | zero => rfl
        | succ n => rw [e] at h; simp at h
      rw [this] at h; simp at h

theorem get_snoc_none {evs : List E} {t : List (Option E)} (ht : t = [] ∨ t = [none]) {i : Nat}
    (h : (evs.map some ++ t)[i]? = some none) : i = evs.length ∧ t = [none] := by
  by_cases hi : i < evs.length
  · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map] at h
    simp at h
  · rw [List.getElem?_append_right (by simp; omega)] at h
    rcases ht with rfl | rfl
    · simp at h
    · refine ⟨?_, rfl⟩
      cases e : i - (evs.map some).length with
      | zero => simp at e; omega
      | succ n => rw [e] at h; simp at h

theorem mem_snoc_some {evs : List E} {t : List (Option E)} (ht : t = [] ∨ t = [none]) {a : E}
    (h : some a ∈ evs.map some ++ t) : a ∈ evs := by
  rcases List.mem_append.mp h with h | h
  · simpa using h
  · rcases ht with rfl | rfl <;> simp at h

theorem inEvents_snoc {e : E} : inEvents (x.snoc k r cv) (some e) ↔ inEvents x e := by
  constructor
  · rintro ⟨rec, hrec, he⟩
    obtain ⟨i, er, hi, rfl⟩ := mem_snoc_records hrec
    exact ⟨er, List.mem_of_getElem? hi, mem_snoc_some (snoc_tail k i) he⟩
  · rintro ⟨er, her, he⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp her
    refine ⟨EventsRecord.snoc k i er, List.mem_iff_getElem?.mpr ⟨i, by rw [snoc_records_get, hi]; rfl⟩, ?_⟩
    exact List.mem_append_left _ (List.mem_map_of_mem he)

theorem inEvents_snoc_none (hk : k < x.records.length) : inEvents (x.snoc k r cv) none := by
  obtain ⟨er, her⟩ : ∃ er, x.records[k]? = some er := ⟨_, List.getElem?_eq_getElem hk⟩
  refine ⟨EventsRecord.snoc k k er, List.mem_iff_getElem?.mpr ⟨k, by rw [snoc_records_get, her]; rfl⟩, ?_⟩
  simp [EventsRecord.snoc]

theorem inSdb_snoc {e : E} : inSdb (x.snoc k r cv) (some e) ↔ inSdb x e := by
  unfold inSdb; rw [inEvents_snoc]; rfl

/-- The relations of `x.snoc k r cv` between old events and into the new one. -/
def Into (P : Rel E) (Q : E → Prop) : Rel (Option E)
  | some a, some b => P a b
  | some a, none => Q a
  | none, _ => False

theorem agentOrder_snoc {a b : Option E} (h : agentOrder (x.snoc k r cv) a b) :
    Into (agentOrder x) (inEvents x) a b := by
  obtain ⟨rec, hrec, -, -, i, j, hij, hi, hj⟩ := h
  obtain ⟨n, er, hn, rfl⟩ := mem_snoc_records hrec
  have ht := snoc_tail (E := E) k n
  have her := List.mem_of_getElem? hn
  match a, b with
  | some a, some b =>
    exact ⟨er, her, List.mem_of_getElem? (get_snoc_some ht hi), List.mem_of_getElem? (get_snoc_some ht hj),
      i, j, hij, get_snoc_some ht hi, get_snoc_some ht hj⟩
  | some a, none => exact ⟨er, her, List.mem_of_getElem? (get_snoc_some ht hi)⟩
  | none, b =>
    obtain ⟨rfl, hl⟩ := get_snoc_none ht hi
    unfold EventsRecord.snoc at hj; rw [hl, List.getElem?_append_right (by simp; omega)] at hj
    cases e : j - (er.events.map some).length with
    | zero => simp at e; omega
    | succ m => rw [e] at hj; simp at hj

theorem rbf_snoc_some {rbf : Rbf E} {ws : List E} {a : Option E} {w : Option E} (h : w ∈ rbf.snoc ws a) :
    ∃ w', w = some w' := by
  cases a <;> simp only [Rbf.snoc, List.mem_map] at h <;> obtain ⟨w', -, rfl⟩ := h <;> exact ⟨w', rfl⟩

variable {rbf : Rbf E} {hsw : Rel E} {ws : List E} {mo : Rel E}

theorem sync_snoc_some {a b : E} (h : SyncWith (x.snoc k r cv) (rbf.snoc ws) (Rel.lift hsw) (some a) (some b)) :
    SyncWith x rbf hsw a b := by
  cases h with
  | rf hrf ho hw he =>
    obtain ⟨h₁, h₂, h₃⟩ := hrf
    exact .rf ⟨inSdb_snoc.mp h₁, inSdb_snoc.mp h₂, by simpa [Rbf.snoc] using h₃⟩ ho hw he
  | agent rec hrec hp =>
    obtain ⟨i, er, hi, rfl⟩ := mem_snoc_records hrec
    simp only [EventsRecord.snoc, List.mem_map, Prod.mk.injEq] at hp
    obtain ⟨p, hp, h₁, h₂⟩ := hp
    cases h₁; cases h₂
    exact .agent er (List.mem_of_getElem? hi) hp
  | host h => exact .host h

theorem sync_snoc {a b : Option E} (hws : ∀ w ∈ ws, inSdb x w)
    (h : SyncWith (x.snoc k r cv) (rbf.snoc ws) (Rel.lift hsw) a b) :
    Into (SyncWith x rbf hsw) (inEvents x) a b := by
  match a, b with
  | some a, some b => exact sync_snoc_some h
  | some a, none =>
    cases h with
    | rf hrf _ _ _ =>
      have := hrf.2.2; simp only [Rbf.snoc, List.mem_map] at this
      obtain ⟨w, hw, he⟩ := this; exact Option.some.inj he ▸ (hws w hw).1
    | agent rec hrec hp =>
      obtain ⟨i, er, -, rfl⟩ := mem_snoc_records hrec
      simp [EventsRecord.snoc] at hp
    | host h => exact h.elim
  | none, b =>
    cases h with
    | rf hrf _ _ _ => obtain ⟨w, hw⟩ := rbf_snoc_some hrf.2.2; cases hw
    | agent rec hrec hp =>
      obtain ⟨i, er, -, rfl⟩ := mem_snoc_records hrec
      simp [EventsRecord.snoc] at hp
    | host h => exact h.elim

/-- Happens-before of `x.snoc k r cv`: happens-before of `x` between old events, and into the new
event only from an event of `x`. -/
theorem hb_snoc (hmo : MemoryOrder x rbf hsw mo) (hws : ∀ w ∈ ws, inSdb x w) (hro : r.order ≠ .init)
    {a b : Option E} (h : HB (x.snoc k r cv) (rbf.snoc ws) (Rel.lift hsw) a b) :
    Into (HB x rbf hsw) (inEvents x) a b := by
  induction h with
  | agent h =>
    have := agentOrder_snoc h
    rename_i a b
    match a, b, this with
    | some _, some _, h => exact .agent h
    | some _, none, h => exact h
  | sync h =>
    have := sync_snoc hws h
    rename_i a b
    match a, b, this with
    | some _, some _, h => exact .sync h
    | some _, none, h => exact h
  | init ha hb ho ho' =>
    rename_i a b
    match a, b with
    | some a, some b => exact .init (inSdb_snoc.mp ha) (inSdb_snoc.mp hb) ho ho'
    | some a, none => exact (inSdb_snoc.mp ha).1
    | none, _ => exact absurd ho hro
  | trans _ _ ih₁ ih₂ =>
    rename_i a b c _ _
    match a, b, c, ih₁, ih₂ with
    | some _, some _, some _, h₁, h₂ => exact .trans h₁ h₂
    | some _, none, some _, h₁, h₂ => exact (hmo.dom _ _ (hmo.hb _ _ h₁)).1
    | some _, none, none, h₁, h₂ => exact h₁
    | some _, some _, none, _, h₂ => exact h₂.elim

/-! ComposeWriteEventBytes and ValueOfReadEvent of the old events. -/

mutual
theorem compose_snoc {loc : M.Math} {ws' : List E} {bs : List M.Math} (h : Compose x rbf loc ws' bs) :
    Compose (x.snoc k r cv) (rbf.snoc ws) loc (ws'.map some) bs :=
  match h with
  | .nil => .nil
  | .write hr hk ha hc => .write hr hk ha (compose_snoc hc)
  | .rmw hr hk hv hm ha hc => .rmw hr hk (valueOf_snoc hv) hm ha (compose_snoc hc)

theorem valueOf_snoc {e : E} {v : List M.Math} (h : ValueOf x rbf e v) :
    ValueOf (x.snoc k r cv) (rbf.snoc ws) (some e) v :=
  match h with
  | .mk hw hl hc => .mk (fun w hw' => by
      simp only [Rbf.snoc, List.mem_map] at hw'
      obtain ⟨w', hw', rfl⟩ := hw'; exact hw w' hw') (by simpa [Rbf.snoc, Exec.snoc] using hl) (compose_snoc hc)
end

/-! Memory ranges of events with non-negative integer [[ByteIndex]] and [[ElementSize]]. -/

/-- The facts of the non-negative integers the proofs use. -/
structure IntFacts (M : Model) : Prop where
  eq_ofNat : ∀ a b, M.eq (M.ofNat a) (M.ofNat b) = decide (a = b)
  lt_ofNat : ∀ a b, M.lt (M.ofNat a) (M.ofNat b) = decide (a < b)
  add_ofNat : ∀ a b, M.add (M.ofNat a) (M.ofNat b) = M.ofNat (a + b)
  isInt_ofNat : ∀ a, M.isInt (M.ofNat a) = true

theorem Model.Laws.intFacts (L : M.Laws) : IntFacts M where
  eq_ofNat a b := by
    by_cases h : a = b
    · subst h; simp [(L.eq_iff _ _).mpr rfl]
    · simp only [h, decide_false]; cases e : M.eq (M.ofNat a) (M.ofNat b) with
      | false => rfl
      | true => exact absurd (L.ofNat_inj ((L.eq_iff _ _).mp e)) h
  lt_ofNat a b := by
    by_cases h : a < b
    · simp [h, L.ofNat_lt_of_lt h]
    · simp only [h, decide_false]; cases e : M.lt (M.ofNat a) (M.ofNat b) with
      | false => rfl
      | true => exact absurd (L.ofNat_lt_iff.mp e) h
  add_ofNat a b := (L.ofNat_add a b).symm
  isInt_ofNat a := (L.isInt_iff _).mpr ⟨a, .inl rfl⟩

/-- An event's [[ByteIndex]] and [[ElementSize]] are non-negative integers. -/
def FormedAt (y : Exec M E) (e : E) : Prop := (∃ n, y.byteIndex e = M.ofNat n) ∧ ∃ n, y.elementSize e = M.ofNat n

theorem eq_of_ofNat (F : IntFacts M) {a b : Nat} (h : M.eq (M.ofNat a) (M.ofNat b) = true) : a = b := by
  rw [F.eq_ofNat] at h; exact of_decide_eq_true h

theorem inRange_of_eq (F : IntFacts M) {y : Exec M E} {a b : E} {loc : M.Math} (hfa : FormedAt y a)
    (hfb : FormedAt y b) (h : rangesEqual y a b) (ha : inRange y a loc) : inRange y b loc := by
  obtain ⟨-, h₁, h₂⟩ := h
  obtain ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ := hfa; obtain ⟨⟨n', hn'⟩, ⟨m', hm'⟩⟩ := hfb
  rw [hn, hn'] at h₁; rw [hm, hm'] at h₂
  obtain rfl := eq_of_ofNat F h₁; obtain rfl := eq_of_ofNat F h₂
  unfold inRange at *; rw [hn', hm', ← hn, ← hm]; exact ha

theorem rangesEqual_symm (F : IntFacts M) {y : Exec M E} {a b : E} (hfa : FormedAt y a) (hfb : FormedAt y b)
    (h : rangesEqual y a b) : rangesEqual y b a := by
  obtain ⟨h₀, h₁, h₂⟩ := h
  obtain ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ := hfa; obtain ⟨⟨n', hn'⟩, ⟨m', hm'⟩⟩ := hfb
  rw [hn, hn'] at h₁; rw [hm, hm'] at h₂
  obtain rfl := eq_of_ofNat F h₁; obtain rfl := eq_of_ofNat F h₂
  exact ⟨h₀.symm, by rw [hn', hn]; exact h₁, by rw [hm', hm]; exact h₂⟩

/-- Byte `i` of an `n`-byte event from a non-negative integer index is in its memory range. -/
theorem inRange_own (F : IntFacts M) {y : Exec M E} {e : E} {n i len : Nat} (hn : y.byteIndex e = M.ofNat n)
    (hl : y.elementSize e = M.ofNat len) (hi : i < len) : inRange y e (M.add (y.byteIndex e) (M.ofNat i)) := by
  unfold inRange; rw [hn, hl, F.add_ofNat, F.add_ofNat, F.lt_ofNat, F.lt_ofNat]
  exact ⟨F.isInt_ofNat _, by simp, by simp; omega⟩

/-! The new event and Lists. -/

theorem mem_getElem? {α : Type} {l : List α} {a : α} (h : a ∈ l) : ∃ i : Nat, l[i]? = some a :=
  List.mem_iff_getElem?.mp h

theorem chosen_snoc_get {i : Nat} {c : Option E × List M.Math} (h : (x.snoc k r cv).chosen[i]? = some c) :
    (∃ e v, c = (some e, v) ∧ x.chosen[i]? = some (e, v)) ∨ (i = x.chosen.length ∧ c = (none, cv)) := by
  simp only [Exec.snoc] at h
  by_cases hi : i < x.chosen.length
  · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map] at h
    obtain ⟨⟨e, v⟩, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inl ⟨e, v, rfl, he⟩
  · rw [List.getElem?_append_right (by simp; omega)] at h
    cases e : i - (x.chosen.map fun c => (some c.1, c.2)).length with
    | zero => rw [e] at h; simp at h e; exact .inr ⟨by omega, h.symm⟩
    | succ m => rw [e] at h; simp at h

/-- **A read last in memory order keeps an execution valid.** `x` is a valid execution with `rbf`,
`hsw` and memory order `mo`; the read `r` appended to its `k`th Agent Events Record reads byte `i`
from `ws[i]`, a write of `x` on its block with byte _byteIndex_ + `i` in its memory range, memory-order
after every other such write; its Chosen Value Record has the bytes they compose. Then `x` with the
read is a valid execution with the read last in memory order. -/
theorem snoc_valid (F : IntFacts M) (hv : ValidWith x rbf hsw) (hmo : MemoryOrder x rbf hsw mo)
    (hf : ∀ e, inSdb x e → FormedAt x e) (hsz : ∃ m, r.elementSize = M.ofNat m)
    (hk : k < x.records.length) (hr : r.IsRead) (hlen : M.eq (M.ofNat ws.length) r.elementSize = true)
    (hws : ∀ (i : Nat) w, ws[i]? = some w → inSdb x w ∧ isWrite x w ∧ x.block w = r.block ∧
      inRange x w (M.add r.byteIndex (M.ofNat i)))
    (hlast : ∀ (i : Nat) w v, ws[i]? = some w → inSdb x v → isWrite x v → x.block v = r.block →
      inRange x v (M.add r.byteIndex (M.ofNat i)) → v ≠ w → mo v w)
    (hc : Compose x rbf r.byteIndex ws cv) (hcv : ∀ c ∈ cv, ∃ n, c = M.ofNat n) :
    ValidWith (x.snoc k r cv) (rbf.snoc ws) (Rel.lift hsw) ∧
      MemoryOrder (x.snoc k r cv) (rbf.snoc ws) (Rel.lift hsw) (Rel.snoc x mo) := by
  have hwsm : ∀ w ∈ ws, inSdb x w := fun w h => by
    obtain ⟨i, hi⟩ := mem_getElem? h; exact (hws i w hi).1
  have hhb := fun {a b} (h : HB (x.snoc k r cv) (rbf.snoc ws) (Rel.lift hsw) a b) => hb_snoc hmo hwsm hr.order h
  have hirr := hmo.order.irrefl
  have hnone : inSdb (x.snoc k r cv) none := ⟨inEvents_snoc_none hk, by
    rcases hr.kind with h | h <;> simp [isSdb, Exec.snoc, h]⟩
  obtain ⟨n, hn⟩ := hr.byteIndex
  have hlenE : r.elementSize = M.ofNat ws.length := by
    obtain ⟨m, hm⟩ := hsz; rw [hm] at hlen ⊢; rw [eq_of_ofNat F hlen]
  have hf' : ∀ e, inSdb (x.snoc k r cv) e → FormedAt (x.snoc k r cv) e := by
    intro e he; match e with
    | some e => exact hf e (inSdb_snoc.mp he)
    | none => exact ⟨⟨n, hn⟩, ⟨_, hlenE⟩⟩
  -- a write of the new read's byte `i` is memory-order before `ws[i]`
  have hown : ∀ (i : Nat) w, ws[i]? = some w → ∀ v, isWrite x v → x.block v = r.block →
      inRange x v (M.add r.byteIndex (M.ofNat i)) → mo w v → False := by
    intro i w hw v hvw hvb hvr hm
    have hv : inSdb x v := ⟨(hmo.dom _ _ hm).2, by rcases hvw with h | h <;> simp [isSdb, h]⟩
    exact hirr _ (hmo.order.trans _ _ _ hm (hlast i w v hw hv hvw hvb hvr fun e => hirr _ (e ▸ hm)))
  -- the bytes of the new read are in the memory range of an event with an equal range
  have hrange : ∀ (i : Nat) w v, ws[i]? = some w → inSdb (x.snoc k r cv) v → rangesEqual (x.snoc k r cv) v none →
      inRange (x.snoc k r cv) v (M.add r.byteIndex (M.ofNat i)) := by
    intro i w v hw hvs he
    have hi : i < ws.length := (List.getElem?_eq_some_iff.mp hw).1
    exact inRange_of_eq F (hf' _ hnone) (hf' _ hvs) (rangesEqual_symm F (hf' _ hvs) (hf' _ hnone) he)
      (inRange_own (y := x.snoc k r cv) (e := none) F hn hlenE hi)
  have hmo' : MemoryOrder (x.snoc k r cv) (rbf.snoc ws) (Rel.lift hsw) (Rel.snoc x mo) := {
    order := ⟨fun a => by cases a with | none => exact id | some a => exact hirr a, by
      intro a b c h₁ h₂
      match a, b, c with
      | some a, some b, some c => exact hmo.order.trans _ _ _ h₁ h₂
      | some a, some b, none => exact (hmo.dom _ _ h₁).1
      | some _, none, _ => exact h₂.elim
      | none, _, _ => exact h₁.elim⟩
    total := by
      intro a b ha hb hne
      match a, b with
      | some a, some b => exact hmo.total a b (inEvents_snoc.mp ha) (inEvents_snoc.mp hb) (fun e => hne (e ▸ rfl))
      | some a, none => exact .inl (inEvents_snoc.mp ha)
      | none, some b => exact .inr (inEvents_snoc.mp hb)
      | none, none => exact absurd rfl hne
    dom := by
      intro a b h
      match a, b with
      | some a, some b =>
        exact ⟨inEvents_snoc.mpr (hmo.dom _ _ h).1, inEvents_snoc.mpr (hmo.dom _ _ h).2⟩
      | some a, none => exact ⟨inEvents_snoc.mpr h, inEvents_snoc_none hk⟩
      | none, _ => exact h.elim
    hb := by
      intro a b h
      have := hhb h
      match a, b with
      | some a, some b => exact hmo.hb _ _ this
      | some a, none => exact this
      | none, _ => exact this.elim
    sc := by
      intro r' w' hrf
      obtain ⟨w, rfl⟩ := rbf_snoc_some hrf.2.2
      rintro ⟨v, hvs, hvw, hvo, hm₁, hm₂, hcase⟩
      match r', v with
      | _, none => exact hm₂.elim
      | some r₀, some v₀ =>
        refine hmo.sc r₀ w ⟨inSdb_snoc.mp hrf.1, inSdb_snoc.mp hrf.2.1, by simpa [Rbf.snoc] using hrf.2.2⟩
          ⟨v₀, inSdb_snoc.mp hvs, hvw, hvo, hm₁, hm₂, ?_⟩
        rcases hcase with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
        · exact .inl ⟨sync_snoc_some h₁, h₂⟩
        · exact .inr (.inl ⟨hhb h₁, hhb h₂, h₃, h₄⟩)
        · exact .inr (.inr ⟨hhb h₁, hhb h₂, h₃, h₄⟩)
      | none, some v₀ =>
        have hw := hrf.2.2; simp only [Rbf.snoc, List.mem_map] at hw
        obtain ⟨w₀, hw₀, he⟩ := hw; cases he
        obtain ⟨i, hi⟩ := mem_getElem? hw₀
        have hwi := hws i w hi
        rcases hcase with ⟨-, h₂⟩ | ⟨-, -, -, h₄⟩ | ⟨-, -, -, h₄⟩
        · exact hown i w hi v₀ hvw h₂.1 (hrange i w (some v₀) hi hvs h₂) hm₁
        · exact hown i w hi v₀ hvw (h₄.1.symm.trans hwi.2.2.1)
            (inRange_of_eq F (hf w hwi.1) (hf v₀ (inSdb_snoc.mp hvs)) h₄ hwi.2.2.2) hm₁
        · exact hown i w hi v₀ hvw h₄.1 (hrange i w (some v₀) hi hvs h₄) hm₁
    finite := by
      intro w' hws' hww hwo
      match w' with
      | some w =>
        obtain ⟨l, hl⟩ := hmo.finite w (inSdb_snoc.mp hws') hww hwo
        refine ⟨l.map some, fun r' hr₁ hr₂ hr₃ hr₄ => ?_⟩
        match r' with
        | some r₀ => exact List.mem_map_of_mem (hl r₀ (inSdb_snoc.mp hr₁) hr₂ hr₃ hr₄)
        | none => exact hr₄.elim
      | none =>
        refine ⟨(x.records.flatMap (·.events)).map some, fun r' _ _ _ hr₄ => ?_⟩
        match r' with
        | some r₀ =>
          obtain ⟨er, her, he⟩ := hr₄
          exact List.mem_map_of_mem (List.mem_flatMap.mpr ⟨er, her, he⟩)
        | none => exact hr₄.elim }
  refine ⟨{
    hostSync := ?_
    readsBytesFrom := ?_
    happensBefore := ⟨fun a h => ?_, fun _ _ _ h₁ h₂ => .trans h₁ h₂⟩
    validChosenReads := ?_
    coherentReads := ?_
    tearFreeReads := ?_
    seqCstAtomics := ⟨_, hmo'⟩ }, hmo'⟩
  · -- host-synchronizes-with
    obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := hv.hostSync
    refine ⟨⟨fun a => ?_, fun a b c => ?_⟩, fun a b h => ?_, fun a h => ?_⟩
    · cases a with | none => exact id | some a => exact h₁ a
    · intro hab hbc
      match a, b, c with
      | some a, some b, some c => exact h₂ a b c hab hbc
      | none, _, _ | some _, none, _ => exact hab.elim
      | some _, some _, none => exact hbc.elim
    · match a, b with
      | some a, some b =>
        obtain ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩ := h₃ a b h
        exact ⟨⟨inEvents_snoc.mpr ha, fun e => ha' (inSdb_snoc.mp e)⟩,
          ⟨inEvents_snoc.mpr hb, fun e => hb' (inSdb_snoc.mp e)⟩⟩
    · have key : ∀ a b, Plus (fun a b => Rel.lift hsw a b ∨ agentOrder (x.snoc k r cv) a b) a b →
          Into (Plus fun a b => hsw a b ∨ agentOrder x a b) (fun _ => True) a b := by
        intro a b h
        induction h with
        | step h =>
          rename_i a b
          rcases h with h | h
          · match a, b with
            | some _, some _ => exact .step (.inl h)
          · have := agentOrder_snoc h
            match a, b with
            | some _, some _ => exact .step (.inr this)
            | some _, none => trivial
            | none, _ => exact this.elim
        | trans _ _ ih₁ ih₂ =>
          rename_i a b c _ _
          match a, b, c with
          | some _, some _, some _ => exact .trans ih₁ ih₂
          | some _, _, none => trivial
          | some _, none, some _ => exact ih₂.elim
          | none, _, _ => exact ih₁.elim
      have := key a a h
      match a with
      | some a => exact h₄ a this
      | none => exact this
  · -- reads-bytes-from
    intro r' h₁ h₂
    match r' with
    | some r₀ =>
      obtain ⟨hl, hw, hi, hn'⟩ := hv.readsBytesFrom r₀ (inSdb_snoc.mp h₁) h₂
      refine ⟨by simpa [Rbf.snoc, Exec.snoc] using hl, fun w hw' => ?_, fun i w hw' => ?_, ?_⟩
      · simp only [Rbf.snoc, List.mem_map] at hw'
        obtain ⟨w₀, hw₀, rfl⟩ := hw'
        exact ⟨inSdb_snoc.mpr (hw w₀ hw₀).1, (hw w₀ hw₀).2⟩
      · simp only [Rbf.snoc, List.getElem?_map, Option.map_eq_some_iff] at hw'
        obtain ⟨w₀, hw₀, rfl⟩ := hw'
        exact hi i w₀ hw₀
      · simpa [Rbf.snoc] using hn'
    | none =>
      refine ⟨by simpa [Rbf.snoc, Exec.snoc] using hlen, fun w hw' => ?_, fun i w hw' => ?_, by simp [Rbf.snoc]⟩
      · simp only [Rbf.snoc, List.mem_map] at hw'
        obtain ⟨w₀, hw₀, rfl⟩ := hw'
        obtain ⟨i, hi⟩ := mem_getElem? hw₀
        exact ⟨inSdb_snoc.mpr (hws i w₀ hi).1, (hws i w₀ hi).2.1⟩
      · simp only [Rbf.snoc, List.getElem?_map, Option.map_eq_some_iff] at hw'
        obtain ⟨w₀, hw₀, rfl⟩ := hw'
        exact ⟨(hws i w₀ hw₀).2.2.1, (hws i w₀ hw₀).2.2.2⟩
  · -- happens-before is irreflexive
    have := hhb h
    match a with
    | some a => exact hv.happensBefore.irrefl a this
    | none => exact this
  · -- valid chosen reads
    intro r' h₁ h₂
    match r' with
    | some r₀ =>
      obtain ⟨i, cv₀, hi, hu, v, hval, hl, hb⟩ := hv.validChosenReads r₀ (inSdb_snoc.mp h₁) h₂
      have hi' : x.chosen.length > i := (List.getElem?_eq_some_iff.mp hi).1
      refine ⟨i, cv₀, ?_, fun j cv' hj => ?_, v, valueOf_snoc hval, hl, hb⟩
      · simp only [Exec.snoc]; rw [List.getElem?_append_left (by simpa using hi'), List.getElem?_map, hi]; rfl
      · rcases chosen_snoc_get hj with ⟨e, v', he, hj'⟩ | ⟨-, he⟩
        · simp only [Prod.mk.injEq, Option.some.injEq] at he
          obtain ⟨rfl, rfl⟩ := he; exact hu j _ hj'
        · simp at he
    | none =>
      refine ⟨x.chosen.length, cv, ?_, fun j cv' hj => ?_, cv, ?_, rfl, fun i a b ha hb => ?_⟩
      · simp [Exec.snoc]
      · rcases chosen_snoc_get hj with ⟨e, v', he, -⟩ | ⟨hj, -⟩
        · simp at he
        · exact hj
      · refine .mk (fun w hw' => ?_) (by simpa [Rbf.snoc, Exec.snoc] using hlen) (compose_snoc hc)
        simp only [Rbf.snoc, List.mem_map] at hw'
        obtain ⟨w₀, hw₀, rfl⟩ := hw'
        obtain ⟨i, hi⟩ := mem_getElem? hw₀
        exact (hws i w₀ hi).2.1
      · rw [ha] at hb; cases hb
        obtain ⟨n, rfl⟩ := hcv a (List.mem_of_getElem? ha)
        rw [F.eq_ofNat]; simp
  · -- coherent reads
    intro r' h₁ h₂ i w' hw'
    match r' with
    | some r₀ =>
      simp only [Rbf.snoc, List.getElem?_map, Option.map_eq_some_iff] at hw'
      obtain ⟨w, hw, rfl⟩ := hw'
      obtain ⟨c₁, c₂⟩ := hv.coherentReads r₀ (inSdb_snoc.mp h₁) h₂ i w hw
      refine ⟨fun h => c₁ (hhb h), ?_⟩
      rintro ⟨v, hvw, hvb, hvr, hb₁, hb₂⟩
      match v with
      | some v₀ => exact c₂ ⟨v₀, hvw, hvb, hvr, hhb hb₁, hhb hb₂⟩
      | none => exact (hhb hb₂).elim
    | none =>
      simp only [Rbf.snoc, List.getElem?_map, Option.map_eq_some_iff] at hw'
      obtain ⟨w, hw, rfl⟩ := hw'
      refine ⟨fun h => (hhb h).elim, ?_⟩
      rintro ⟨v, hvw, hvb, hvr, hb₁, hb₂⟩
      match v with
      | some v₀ => exact hown i w hw v₀ hvw hvb hvr (hmo.hb _ _ (hhb hb₁))
      | none => exact (hhb hb₂).elim
  · -- tear free reads
    intro r' h₁ h₂ h₃
    match r' with
    | some r₀ =>
      obtain ⟨ha, ht⟩ := hv.tearFreeReads r₀ (inSdb_snoc.mp h₁) h₂ h₃
      refine ⟨ha, fun w' hrf hnt => ?_⟩
      obtain ⟨w, rfl⟩ := rbf_snoc_some hrf.2.2
      rintro ⟨he, v', hv', hvt, hne, hrv⟩
      obtain ⟨v, rfl⟩ := rbf_snoc_some hrv.2.2
      have hrf₀ : readsFrom x rbf r₀ w := ⟨inSdb_snoc.mp hrf.1, inSdb_snoc.mp hrf.2.1, by simpa [Rbf.snoc] using hrf.2.2⟩
      have hrv₀ : readsFrom x rbf r₀ v := ⟨inSdb_snoc.mp hrv.1, inSdb_snoc.mp hrv.2.1, by simpa [Rbf.snoc] using hrv.2.2⟩
      exact ht w hrf₀ hnt ⟨he, v, hv', hvt, fun e => hne (e ▸ rfl), hrv₀⟩
    | none =>
      refine ⟨hr.aligned h₃, fun w' hrf _ => ?_⟩
      rintro ⟨-, v', hv', -, hne, hrv⟩
      have hw := hrf.2.2; have hv := hrv.2.2
      simp only [Rbf.snoc, List.mem_map] at hw hv
      obtain ⟨w, hw, rfl⟩ := hw; obtain ⟨v, hv, rfl⟩ := hv
      obtain ⟨i, hi⟩ := mem_getElem? hw; obtain ⟨j, hj⟩ := mem_getElem? hv
      have hwi := hws i w hi; have hvj := hws j v hj
      have hvw : rangesEqual x v w := hv'
      have hfw := hf w hwi.1; have hfv := hf v hvj.1
      have h₁ : mo w v := hlast j v w hj hwi.1 hwi.2.1 hwi.2.2.1 (inRange_of_eq F hfv hfw hvw hvj.2.2.2)
        (fun e => hne (e ▸ rfl))
      have h₂ : mo v w := hlast i w v hi hvj.1 hvj.2.1 hvj.2.2.1
        (inRange_of_eq F hfw hfv (rangesEqual_symm F hfv hfw hvw) hwi.2.2.2) (fun e => hne (e ▸ rfl))
      exact hirr _ (hmo.order.trans _ _ _ h₁ h₂)


/-! Law L2's claim is not vacuous. -/

end Ecma.MemoryModel
