module

public import Engine.Proofs.Step.Sym
public import Engine.Proofs.Step.Table
public import Engine.Proofs.Step.Rows.CodePoints

@[expose] public section

/-!
# StringToCodePoints's row

The engine's shortcut at StringToCodePoints (`Engine.Accel.stcpEntry`: one scan of the String's code units, the
List of the code points in one cell and then one CodePointAt Record for each) is the specification's steps:
`stcp_algRow`. The steps call CodePointAt (`cpa_steps`, `Rows/CodePoints.lean`); the loop is `stcp_loop`, by
induction on the scan's fuel.
-/

namespace Engine.Machine

open Ecma Ecma.Machine

variable (H : Host F) (chk : Bool)

/-! ## StringToCodePoints's loop -/

/-- The loop, at round `r`. -/
def stcpLoop (r : Nat) : Loop F :=
  { x := none,
    it := Iter.while_ (Op.leaf (Leaf.rel RelOp.lt) [Op.var 3, Op.var 2]),
    p := [4],
    body :=
      [Ins.site [1, 4],
        Ins.let_ 4 (Op.call (CallK.alg { clause := Known.cCodePointAt, idx := 0 }) [Op.var 0, Op.var 3]),
        Ins.site [2, 4],
        Ins.eval (Op.call (CallK.prim Known.pAppend) [Op.leaf (Leaf.field Known.fCodePoint) [Op.var 4], Op.bnd 1]),
        Ins.site [3, 4],
        Ins.let_ 3 (Op.leaf (Leaf.bin BinOp.add) [Op.var 3, Op.leaf (Leaf.field Known.fCodeUnitCount) [Op.var 4]])],
    st := IterSt.plain, r := r }

/-- The state with the List of the code points `cs` and the Records `rs` allocated. -/
def stcpSt (st : State F) (cs : Array (Val F)) (rs : Array (Cell F)) : State F :=
  { st with heap := (st.heap.push (.list cs 0)).pushMany rs }

/-- The loop's end and the return, where the position is not below the size. -/
theorem stcp_end (st : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (s : Array UInt16)
    (p : Nat) (cs : Array (Val F)) (rs : Array (Cell F)) (v4 : Val F) (q : List Nat) (r : Nat) (hp : ¬ p < s.size) :
    Steps (Ctx.spec Engine.P' H chk) ⟨stcpSt st cs rs,
        ⟨a, nd, #[.str s, .ref st.heap.next, .math (.int s.size), .math (.int p), v4], .steps false true true, q,
          [.seq [.site [5], .ret (.var 1)]], none⟩ :: fs, .loop .round (stcpLoop r)⟩
      ⟨stcpSt st cs rs, fs, .val (.ref st.heap.next)⟩ := by
  gsteps
  refine Steps.valBool false (by mdecide) ?_
  gsteps
  exact .refl _

open Engine.Accel in
theorem stcp_loop [PinsHold] (st : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (s : Array UInt16) :
    ∀ (k p : Nat) (cs : Array (Val F)) (rs : Array (Cell F)) (v4 : Val F) (q : List Nat) (r : Nat), s.size - p ≤ k →
    Steps (Ctx.spec Engine.P' H chk) ⟨stcpSt st cs rs,
        ⟨a, nd, #[.str s, .ref st.heap.next, .math (.int s.size), .math (.int p), v4], .steps false true true, q,
          [.seq [.site [5], .ret (.var 1)]], none⟩ :: fs, .loop .round (stcpLoop r)⟩
      ⟨stcpSt st (scanCps s k p cs rs).1 (scanCps s k p cs rs).2, fs, .val (.ref st.heap.next)⟩ := by
  intro k
  induction k with
  | zero =>
    intro p cs rs v4 q r hk
    simp only [scanCps]
    exact stcp_end H chk st fs a nd s p cs rs v4 q r (by omega)
  | succ k ih =>
    intro p cs rs v4 q r hk
    by_cases hp : p < s.size
    · simp only [scanCps, hp, ↓reduceIte]
      unfold stcpSt
      have hc := (cpAt_count s p hp).1
      generalize ht : cpAt s p = t at hc ⊢
      gsteps
      refine Steps.valBool true (by mdecide) ?_
      gsteps
      refine Steps.trans (cpa_steps H chk _ _ s p hp) ?_
      rw [ht]
      gsteps
      refine Steps.next (step_field _ _ _ _ _ _ _ _ _ _ _ _ _ (cpRec_cp _ _ t (heap_push_get _ _))) ?_
      gsteps
      refine Steps.next (step_append _ _ _ _ _ cs 0 rfl (heap_list_get' _ _ _ _)) ?_
      simp only [← Engine.Model.ChunkedHeap.pushMany_push, heap_list_set]
      gsteps
      refine Steps.next (step_field _ _ _ _ _ _ _ _ _ _ _ _ _ (cpRec_count _ _ t (heap_rec_get _ _ _ _ _))) ?_
      iterate 4 gstep
      simp only [↓reduceIte]
      gstep
      have e : ((p + t.2.1 : Nat) : Int) = (p : Int) + (t.2.1 : Int) := by omega
      have h := ih (p + t.2.1) (cs.push (.math (Model.MathVal.int t.1))) (rs.push (cpRec t))
        (.ref ((st.heap.push (.list cs 0)).pushMany rs).next) [3, 4] (r + 1) (by omega)
      unfold stcpSt at h
      rw [e] at h
      exact h
    · simp only [scanCps, hp, ↓reduceIte]
      exact stcp_end H chk st fs a nd s p cs rs v4 q r hp

open Engine.Accel in
/-- StringToCodePoints's steps at a String: a new List of its code points, then CodePointAt's Records. -/
theorem stcp_steps [PinsHold] (st : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (s : Array UInt16) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨st, ⟨a, nd, #[.str s, .unbound, .unbound, .unbound, .unbound], .steps false true true, [], [], none⟩ :: fs,
        .code stcpCode⟩
      ⟨stcpSt st (scanCps s s.size 0 #[] #[]).1 (scanCps s s.size 0 #[] #[]).2, fs, .val (.ref st.heap.next)⟩ := by
  iterate 22 gstep
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h := stcp_loop H chk st fs a nd s s.size 0 #[] #[] .unbound [4] (0 + 1) (by omega)
  unfold stcpSt at h ⊢
  exact h

open Engine.Accel in
/-- The engine's shortcut at StringToCodePoints is the specification's steps, from a configuration whose
transition enters the algorithm's frame. -/
theorem stcp_row [PinsHold] (c : Cfg F) (vs : List (Val F))
    (r : Run F (Option (Val F))) (nd : Option F.Node) (he : stcpEntry vs = some r)
    (hstep : step (Ctx.spec Engine.P' H chk) c =
      enterAlg (Ctx.spec Engine.P' H chk) c stcpAlg nd (stcpAlg.args vs) stcpAlg.header.rc true true) :
    Sim (Ctx.spec Engine.P' H chk) c (bindR c r fun o c => match o with
      | some v => c.to (.val v)
      | none => step (Ctx.spec Engine.P' H chk) c) := by
  unfold stcpEntry at he
  split at he
  · rename_i s
    split at he
    · cases he
      obtain ⟨st, fs, ctl⟩ := c
      show Steps _ _ _
      refine Steps.next hstep ?_
      have hcode : (Ctx.spec Engine.P' H chk).algCode stcpAlg.id = stcpCode := by
        show (Engine.P'.alg ⟨Known.cStringToCodePoints, 0⟩).getD _ = _
        rw [stcpCode_pin]; rfl
      rw [hcode]
      exact stcp_steps H chk st fs _ nd s
    · cases he
  · cases he

open Engine.Accel in
/-- StringToCodePoints's row. -/
theorem stcp_algRow [PinsHold] (H : Host F) (chk : Bool) :
    AlgRow (Ctx.spec Engine.P' H chk) ⟨Known.cStringToCodePoints, 0⟩ Engine.Accel.stcpEntry :=
  ⟨stcpAlg, stcpAlg_pin, fun c vs r nd he hstep => stcp_row H chk c vs r nd he hstep⟩

end Engine.Machine

