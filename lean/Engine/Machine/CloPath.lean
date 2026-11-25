module

public import Ecma.Lower.Lin

@[expose] public section

/-!
# Where a closure literal's steps are numbered

An Abstract Closure literal's steps are numbered under the step that evaluates the literal
(`cloPath`): the closure literals a piece of syntax makes (`closE` … `closS`), and the path of the
step of an algorithm or SDO row that makes a given one.
-/

namespace Engine.Machine
open Ecma Ecma.Machine

mutual
/-- The closure literals an expression holds. -/
partial def closE : Expr → List Nat
  | .closure k => [k]
  | .call _ as | .callAt _ as | .list as => as.flatMap closE
  | .sdo _ e as | .imethod e _ as | .cmethod e _ as | .apply e as => closE e ++ as.flatMap closE
  | .component _ e | .field e _ | .q e | .bang e | .un _ e | .paren e
  | .childOf e _ | .resumedWith e | .tableStep _ e => closE e
  | .index a b | .bin _ a b => closE a ++ closE b
  | .record _ fs => fs.flatMap (closE ·.2)
  | .ofCond cd => closC cd
  | _ => []

/-- The closure literals a condition holds. -/
partial def closC : Cond → List Nat
  | .preds e p rest => closE e ++ closP p ++ rest.flatMap (closP ·.2)
  | .rel _ a b => closE a ++ closE b
  | .and cs | .or cs => cs.flatMap closC
  | .paren cd => closC cd
  | .alg _ | .pass _ => []
  | .expr e => closE e

/-- The closure literals a predicate holds. -/
partial def closP : Pred → List Nat
  | .isVal _ _ es => es.flatMap closE
  | .isTy _ _ ts => ts.flatMap closT
  | .call _ as _ => as.flatMap closE

/-- The closure literals a type holds. -/
partial def closT : TyExpr → List Nat
  | .listOf t | .seqOf t => closT t
  | .butNot a b => closT a ++ closT b
  | .union ts => ts.flatMap closT
  | .completion t => (t.map closT).getD []
  | .interval t lo hi => closT t ++ closE lo ++ closE hi
  | .value e => closE e
  | .record fs => fs.flatMap (closT ·.2)
  | .that t p rest => closT t ++ closP p ++ rest.flatMap (closP ·.2)
  | .pred p => closP p
  | _ => []
end

/-- The closure literals a statement evaluates at its own step (not in its nested steps). -/
def closS : Stmt → List Nat
  | .let_ _ e | .ret (some e) | .perform e | .throwVal e | .suspend e _
  | .push e _ | .remove e _ | .forEachRec _ _ e _ | .forIndex _ e _ | .forChildrenOf _ e _ | .repeatN e _ =>
    closE e
  | .set (.field p _) e | .set (.expr p) e => closE p ++ closE e
  | .set (.var _) e => closE e
  | .if_ cd .. | .ifElse cd .. | .assert cd | .assertAlways cd | .repeatWhile cd _ | .repeatUntil cd _ => closC cd
  | .assertIf cd d => closC cd ++ closC d
  | .forEach _ t l _ _ => (t.map closT).getD [] ++ closE l
  | .forRange _ lo _ hi _ _ _ | .removeRestore lo hi | .resume lo hi | .resumeLet lo hi _
  | .setCodeState lo hi => closE lo ++ closE hi
  | .forKeys _ o cd _ _ => closE o ++ closC cd
  | _ => []

mutual
/-- The step evaluating closure literal `k` among steps `ns` from `i` under `up`, numbered as `step` does. -/
partial def cloPathNs (cs : Array CloLit) (k : Nat) (ns : List Stmt) (i : Nat) (up : List Nat) :
    Option (List Nat) :=
  match ns with
  | [] => none
  | s :: r => (cloPathS cs k i up s).orElse fun _ => cloPathNs cs k r (i + width s) up

/-- The path of closure literal `k` in statement `s` at step `i :: up`. -/
partial def cloPathS (cs : Array CloLit) (k : Nat) (i : Nat) (up : List Nat) (s : Stmt) :
    Option (List Nat) :=
  let p := i :: up
  let own := closS s
  if own.contains k then some p else
  (own.findSome? fun j => cs[j]?.bind fun cl => cloPathNs cs k cl.body 1 p).orElse fun _ =>
  match s with
  | .if_ _ b arms els => (cloPathB cs k i up b).orElse fun _ =>
    (arms ++ els.toList).zipIdx.findSome? fun (Arm.mk cd b, j) =>
      let i' := i + 1 + j
      if ((cd.map closC).getD []).contains k then some (i' :: up) else cloPathB cs k i' up b
  | .ifElse _ s1 s2 => (cloPathS cs k i up s1).orElse fun _ => cloPathS cs k i up s2
  | .repeat_ b | .repeatWhile _ b | .repeatUntil _ b | .repeatN _ b | .block b => cloPathNs cs k b 1 p
  | .forEach _ _ _ _ b | .forEachRec _ _ _ b | .forRange _ _ _ _ _ _ b
  | .forKeys _ _ _ _ b | .forIndex _ _ b | .forChildren _ b | .forChildrenOf _ _ b => cloPathB cs k i up b
  | _ => none

/-- The path of closure literal `k` in a body at step `i :: up`. -/
partial def cloPathB (cs : Array CloLit) (k : Nat) (i : Nat) (up : List Nat) : Body → Option (List Nat)
  | .inline s => cloPathS cs k i up s
  | .block ns => cloPathNs cs k ns 1 (i :: up)
end

/-- The step path a closure's steps are numbered under: its literal's step, in its algorithm or SDO row. -/
def cloPath (P : Prog) (site : CloSite) : List Nat :=
  let code : Option (Array CloLit × List Stmt) := match P.alg site.alg with
    | some g => some (g.closures, g.body)
    | none => (P.rowOf site.alg).map fun (r : SdoRow) => (r.closures, r.body)
  (code.bind fun (cs, b) => cloPathNs cs site.idx b 1 []).getD []

end Engine.Machine
