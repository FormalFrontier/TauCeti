/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Irreducible

/-!
# Connected components

This file records general topological properties of the quotient of a space by its connected
components.

## Main declarations

* `TauCeti.instT1SpaceConnectedComponents`: the connected-components quotient of any topological
  space is a T1 space.
* `TauCeti.finite_connectedComponents_of_finite_irreducibleComponents`: finiteness of the
  irreducible components implies finiteness of the connected components.
-/

public section

open Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

namespace TauCeti

/-- The quotient of a topological space by its connected components is a T1 space. -/
instance instT1SpaceConnectedComponents : T1Space (ConnectedComponents X) :=
  ⟨fun c => by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [← ConnectedComponents.isQuotientMap_coe.isClosed_preimage,
      connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent⟩

/-- A space with finitely many irreducible components has finitely many connected components. -/
theorem finite_connectedComponents_of_finite_irreducibleComponents
    (h : (irreducibleComponents X).Finite) : Finite (ConnectedComponents X) := by
  let C : Set (ConnectedComponents X) :=
    ⋃ Z ∈ irreducibleComponents X, ConnectedComponents.mk '' Z
  have hC : C.Finite := h.biUnion fun Z hZ =>
    Set.Subsingleton.finite <| by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [ConnectedComponents.coe_eq_coe']
      exact hZ.1.isConnected.isPreconnected.subset_connectedComponent hy hx
  have hC_eq : C = Set.univ := by
    rw [eq_univ_iff_forall]
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    have hx : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]
      simp
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx
    exact Set.mem_iUnion_of_mem Z <| Set.mem_iUnion_of_mem hZ ⟨x, hxZ, rfl⟩
  apply Finite.of_finite_univ
  rw [← hC_eq]
  exact hC

end TauCeti
