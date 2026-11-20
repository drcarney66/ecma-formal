module

public import Engine.Model

@[expose] public section

/-! # Impl's restamping: a Parse Node's views but its stamp are its restamping's -/

namespace Engine.Impl

open Engine.Model
open Ecma (Model NtId)

theorem restamp_mk (k : Nat) (st lo hi p nt ps kids t) :
    restamp k (.mk st lo hi p nt ps kids t) = .mk k lo hi p nt ps (kids.map fun c => (c.1, c.2.map (restamp k))) t := by
  rw [restamp]; simp only [Option.map_attach_eq_pmap, Option.pmap_eq_map]
  congr 1
  conv => rhs; rw [← Array.attach_map_subtype_val kids, Array.map_map]
  rfl

theorem nodeKids_restamp (k : Nat) (n : Engine.Model.Node) :
    Engine.Impl.nodeKids (restamp k n) = (Engine.Impl.nodeKids n).map (restamp k) := by
  cases n; rw [restamp_mk]
  show Array.filterMap _ _ = Array.map _ (Array.filterMap _ _)
  rw [Array.filterMap_map, Array.map_filterMap]
  rfl

end Engine.Impl
