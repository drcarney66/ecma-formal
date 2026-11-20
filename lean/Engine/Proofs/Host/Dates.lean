module

public import Engine.Proofs.Host.Laws
public import Engine.Host.DateParse

@[expose] public section

/-!
# Date.parse's parser meets the laws

`dateParse` (`Ecma.DateParse`) reads the Date Time String Format's valid instances and refuses its illegal ones
(`dateIso_units`). A host whose ParseDateString answers by it (`ParsesDates`) meets the laws of its answers
(`ParsesDates.dateFormUTC`, `ParsesDates.dateFormIllegal`).
-/

namespace Ecma

theorem dateDigits_dec (n v : Nat) (r : List Nat) : dateDigits n (decUnits n v ++ r) = some (v % 10 ^ n, r) := by
  induction n with
  | zero => simp [dateDigits, decUnits, Nat.mod_one]
  | succ n ih =>
    have hk : v / 10 ^ n % 10 < 10 := Nat.mod_lt _ (by decide)
    simp only [decUnits, List.cons_append, dateDigits, ih, Option.map_some]
    rw [if_pos (by omega), Nat.mod_pow_succ, Nat.add_sub_cancel_left, Nat.mul_comm, Nat.add_comm]

theorem dateValue_eq {y : Int} {mo d h mi sc ms : Nat} (off : Int) (h1 : 1 ≤ mo) (h2 : mo ≤ 12) (h3 : 1 ≤ d)
    (h4 : d ≤ 31) (h5 : mi ≤ 59) (h6 : sc ≤ 59) (h7 : h < 24 ∨ h = 24 ∧ mi = 0 ∧ sc = 0 ∧ ms = 0) :
    dateValue y mo d h mi sc ms off = some (dateMs y mo d h mi sc ms - off * 60000) :=
  if_pos ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- A date form's UTC offset with `HH` over 23 or `mm` over 59, which `dateOffset` refuses. -/
theorem dateDigits_dec' (n v : Nat) : dateDigits n (decUnits n v) = some (v % 10 ^ n, []) := by
  simpa using dateDigits_dec n v []

/-- A local time has no UTC offset. -/
theorem DateForm.offsetMin_local {f : DateForm} (h : f.isLocal = true) : f.offsetMin = 0 := by
  rcases f with ⟨sign, year, md, time⟩
  cases time with
  | none => simp [DateForm.isLocal] at h
  | some p =>
    simp only [DateForm.isLocal] at h
    simp [DateForm.offsetMin, DateForm.offset, Option.isNone_iff_eq_none.mp h]

def offBad (f : DateForm) : Bool :=
  match f.offset with
  | some (_, h, m) => 23 < h || 59 < m
  | none => false

theorem dateYear_units (f : DateForm) (hf : f.fits) (r : List Nat) :
    dateYear (f.yearPart ++ r) = if f.sign = some true ∧ f.year = 0 then none else some (f.yearInt, r) := by
  rcases f with ⟨_ | _ | _, year, md, time⟩ <;> simp [DateForm.fits] at hf
  · obtain ⟨c, cs, hc, hc48⟩ : ∃ c cs, decUnits 4 year ++ r = c :: cs ∧ 48 ≤ c := ⟨_, _, rfl, by omega⟩
    simp only [DateForm.yearPart]
    rw [hc, dateYear, if_neg (by omega), ← hc, dateDigits_dec]
    simp [DateForm.yearInt, Nat.mod_eq_of_lt hf.1]
  · simp [DateForm.yearPart, DateForm.signUnits, dateYear, dateDigits_dec, DateForm.yearInt,
      Nat.mod_eq_of_lt hf.1]
  · simp [DateForm.yearPart, DateForm.signUnits, dateYear, dateDigits_dec, DateForm.yearInt,
      Nat.mod_eq_of_lt hf.1]

theorem dateField_time (time : Option DateTimePart) : dateField 45 2 1 (DateForm.timePart time) =
    some (1, DateForm.timePart time) := by
  cases time <;> simp [DateForm.timePart, DateForm.timeUnits, dateField]

theorem dateTimePart_units (f : DateForm) (hf : f.fits) : dateTimePart (DateForm.timePart f.time) =
    if offBad f then none else some (f.hour, f.minute, f.second, f.milli, f.offsetMin) := by
  rcases f with ⟨sign, year, md, _ | ⟨h, mi, sec, off⟩⟩
  · simp [DateForm.timePart, dateTimePart, offBad, DateForm.offset, DateForm.hour, DateForm.minute,
      DateForm.second, DateForm.milli, DateForm.offsetMin]
  · simp [DateForm.fits, DateForm.hour, DateForm.minute, DateForm.second, DateForm.milli, DateForm.offset] at hf
    rcases sec with _ | ⟨sc, _ | ms⟩ <;> rcases off with _ | _ | ⟨_ | _, oh, om⟩ <;>
      simp_all [DateForm.timePart, DateForm.timeUnits, DateForm.secPart, DateForm.offUnits, DateForm.signUnits,
        dateTimePart, dateTimeIso, dateSecond, dateField, dateOffset, dateLit, dateDigits_dec, dateDigits_dec',
        Nat.mod_eq_of_lt, offBad, DateForm.offset, DateForm.offsetMin, DateForm.hour, DateForm.minute,
        DateForm.second, DateForm.milli]
    all_goals split <;> simp_all <;> omega

theorem dateField_dec (c n d v : Nat) (r : List Nat) :
    dateField c n d (c :: (decUnits n v ++ r)) = some (v % 10 ^ n, r) := by
  simp [dateField, dateDigits_dec]

/-- `dateIso` of a date form: its fields' time value less its UTC offset, unless the year is
-000000 or the offset is one it refuses. -/
theorem dateIso_units (f : DateForm) (hf : f.fits) :
    dateIso f.units = if (f.sign = some true ∧ f.year = 0) ∨ offBad f = true then none else
      dateValue f.yearInt f.month f.day f.hour f.minute f.second f.milli f.offsetMin := by
  have hy := dateYear_units f hf (DateForm.mdPart f.md ++ DateForm.timePart f.time)
  have ht := dateTimePart_units f hf
  have hmo : f.month < 100 := hf.2.1
  have hd : f.day < 100 := hf.2.2.1
  unfold dateIso DateForm.units
  rw [List.append_assoc, hy]
  by_cases h0 : f.sign = some true ∧ f.year = 0
  · simp [h0]
  · simp only [if_neg h0]
    by_cases hb : offBad f = true
    · rw [if_pos hb] at ht
      rcases hmd : f.md with _ | ⟨mo, _ | d⟩ <;>
        simp [DateForm.mdPart, dateField_dec, dateField_time, ht, hb]
    · rw [if_neg hb] at ht
      rcases hmd : f.md with _ | ⟨mo, _ | d⟩ <;> simp [hmd, DateForm.month, DateForm.day] at hmo hd <;>
        simp [hmd, DateForm.mdPart, dateField_dec, dateField_time, ht, hb, Nat.mod_eq_of_lt, hmo, hd,
          DateForm.month, DateForm.day] <;> exact fun h1 h2 => absurd ⟨h1, h2⟩ h0

/-- A date form's first code unit is a digit or a sign, so `dateParse` reads it as one. -/
theorem dateParse_iso (f : DateForm) : dateParse f.units = dateIso f.units := by
  unfold dateParse
  rw [if_neg]
  rcases f with ⟨_ | _ | _, year, md, time⟩
  · have hk : year / 10 ^ 3 % 10 < 10 := Nat.mod_lt _ (by decide)
    simp [DateForm.units, DateForm.yearPart, decUnits]; omega
  all_goals simp [DateForm.units, DateForm.yearPart, DateForm.signUnits]

/-! A host that answers ParseDateString by `dateParse`. -/

theorem foldl_snoc {α : Type} (acc l : List α) : l.foldl (fun l x => l ++ [x]) acc = acc ++ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp [ih]

section
variable {M : Model}

/-- `r` is `dateParse`'s answer for the code units `l`: its instant's time value, else *NaN*. -/
def DateAnswer (r : Val M) (l : List Nat) : Prop :=
  match dateParse l with
  | some t => tvResult r t
  | none => ∃ n, r = .num n ∧ M.numView n = .nan

/-- `H`'s ParseDateString answers a String by `dateParse` of its code units. -/
def ParsesDates (H : Host M) : Prop :=
  ∀ x s r s' l, H.choice Known.pParseDateString [.str x] s = .ok r s' → unitsAre x l → DateAnswer r l

theorem dateAnswer_some {r : Val M} {l : List Nat} {t : Int} (h : DateAnswer r l) (ht : dateParse l = some t) :
    tvResult r t := by
  unfold DateAnswer at h; rw [ht] at h; exact h

theorem dateAnswer_none {r : Val M} {l : List Nat} (h : DateAnswer r l) (ht : dateParse l = none) :
    ∃ n, r = .num n ∧ M.numView n = .nan := by
  unfold DateAnswer at h; rw [ht] at h; exact h

/-- `dateNumB` decides that `n` is the integral Number `t` and a time value. -/
theorem dateNumB_spec {n : M.Num} {t : Int} (h : dateNumB n t = true) :
    numIs n t ∧ instantTimeValue n ∧ M.numView n ≠ .negZero := by
  unfold dateNumB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hi, hm⟩ := h
  refine ⟨?_, instantB_spec hi, fun hz => by simp [hz] at hm⟩
  unfold numIs
  split at hm
  · rename_i hv
    rw [if_pos (by simpa using hm)]; exact hv
  · rename_i m hv
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hm
    rw [if_neg hm.1]; exact ⟨m, hv, hm.2⟩
  · cases hm

/-- `parseDateNum`'s Number is `dateParse`'s answer, a time value, never -0𝔽. -/
theorem parseDateNum_spec (hnan : M.numView M.numNaN = .nan) {cs : List Nat} {n : M.Num}
    (h : parseDateNum cs = some n) :
    DateAnswer (.num n) cs ∧ (M.numView n = .nan ∨ instantTimeValue n) ∧ M.numView n ≠ .negZero := by
  have hz : M.numView M.numNaN ≠ .negZero := by rw [hnan]; exact fun h => nomatch h
  unfold parseDateNum at h
  unfold DateAnswer
  rcases hd : dateParse cs with _ | t <;> rw [hd] at h <;> dsimp only at h ⊢
  · cases h; exact ⟨⟨_, rfl, hnan⟩, .inl hnan, hz⟩
  · by_cases hin : inTime t = true
    · rw [if_pos hin] at h
      split at h
      · rename_i hb
        cases h
        obtain ⟨h1, h2, h3⟩ := dateNumB_spec hb
        exact ⟨⟨_, rfl, by rw [if_pos hin]; exact h1⟩, .inr h2, h3⟩
      · cases h
    · rw [if_neg hin] at h
      cases h
      exact ⟨⟨_, rfl, by rw [if_neg hin]; exact hnan⟩, .inl hnan, hz⟩

/-- §21.4.3.2 ¶0–1: `dateFormUTC` of a host that parses by `dateParse`. -/
theorem ParsesDates.dateFormUTC {H : Host M} (hA : ParsesDates H) {x : M.Str} {s s' : State M} {r : Val M}
    {f : DateForm} (hp : H.choice Known.pParseDateString [.str x] s = .ok r s') (hfits : f.fits) (hlegal : f.legal)
    (hu : unitsAre x f.units) : tvResult r (f.ms - f.offsetMin * 60000) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hlegal
  have hdm := daysInMonth_le f.yearInt f.month
  have hb : offBad f = false := by
    unfold offBad; split
    · rename_i n oh om ho; have := h8 n oh om ho; simp; omega
    · rfl
  apply dateAnswer_some (hA x s r s' _ hp hu)
  rw [dateParse_iso, dateIso_units f hfits, if_neg (by simp [h9, hb]),
    dateValue_eq _ h1 h2 h3 (by omega) h6 h7 (by omega)]
  rfl

/-- §21.4.3.2 ¶0: `dateFormIllegal` of a host that parses by `dateParse`. -/
theorem ParsesDates.dateFormIllegal {H : Host M} (hA : ParsesDates H) {x : M.Str} {s s' : State M} {r : Val M}
    {f : DateForm} (hp : H.choice Known.pParseDateString [.str x] s = .ok r s') (hfits : f.fits) (hill : f.illegal)
    (hu : unitsAre x f.units) : ∃ n, r = .num n ∧ M.numView n = .nan := by
  apply dateAnswer_none (hA x s r s' _ hp hu)
  rw [dateParse_iso, dateIso_units f hfits]
  split
  · rfl
  · rename_i hn
    unfold dateValue
    rw [if_neg]
    rcases hill with h | h | h | h | h | h | h | ⟨n, oh, om, ho, hh⟩ | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact absurd (by simp [offBad, ho]; omega) hn
    · exact absurd (.inl h) hn

end

end Ecma

