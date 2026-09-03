/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Irreducible
public import TauCeti.Topology.PathComponent
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Connected components

This file records general topological properties of connected components, and of the quotient of a
space by them.

## Main declarations

* `TauCeti.Homeomorph.image_connectedComponent`: a homeomorphism maps a connected component onto
  the connected component of the image point.
* `TauCeti.frontier_connectedComponentIn_subset_compl`: in a locally connected space, a connected
  component of an open set has its frontier in the complement of that set.
* `TauCeti.instT1SpaceConnectedComponents`: the connected-components quotient of any topological
  space is a T1 space.
* `TauCeti.connectedComponentsSigmaHomeomorph`: a locally connected space is homeomorphic
  to the disjoint union of its connected components.
* `TauCeti.finite_connectedComponents_of_finite_irreducibleComponents`: finiteness of the
  irreducible components implies finiteness of the connected components.
-/

public section

open Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

namespace TauCeti

/-- A homeomorphism maps a connected component onto the connected component of the image point. -/
theorem Homeomorph.image_connectedComponent {Y : Type*} [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    e '' connectedComponent x = connectedComponent (e x) := by
  simpa only [connectedComponentIn_univ, Set.image_univ_of_surjective e.surjective] using
    e.image_connectedComponentIn (s := Set.univ) (x := x) (Set.mem_univ x)

/-- **The frontier of a connected component of an open set misses the set.** Equivalently,
`frontier (connectedComponentIn F x) ∩ F = ∅`: the component is clopen in `F`. -/
theorem frontier_connectedComponentIn_subset_compl [LocallyConnectedSpace X] {F : Set X}
    (hF : IsOpen F) (x : X) : frontier (connectedComponentIn F x) ⊆ Fᶜ := by
  intro y hy hyF
  have hC : IsOpen (connectedComponentIn F x) := hF.connectedComponentIn
  obtain ⟨z, hzy, hzx⟩ :=
    mem_closure_iff.mp hy.1 _ hF.connectedComponentIn (mem_connectedComponentIn hyF)
  have hyC : y ∈ connectedComponentIn F x := by
    rw [connectedComponentIn_eq hzx, ← connectedComponentIn_eq hzy]
    exact mem_connectedComponentIn hyF
  exact hy.2 (by rwa [hC.interior_eq])

/-- The quotient of a topological space by its connected components is a T1 space. -/
instance instT1SpaceConnectedComponents : T1Space (ConnectedComponents X) :=
  ⟨fun c => by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [← ConnectedComponents.isQuotientMap_coe.isClosed_preimage,
      connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent⟩

/-- A fibre of the quotient to connected components is path-connected when the ambient space is
locally path-connected. -/
instance instPathConnectedSpaceConnectedComponentsFiber [LocallyPathConnectedSpace X]
    (C : ConnectedComponents X) :
    PathConnectedSpace (ConnectedComponents.mk ⁻¹' {C} : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [connectedComponents_preimage_singleton, ← pathComponent_eq_connectedComponent]
  infer_instance

/-- A fibre of the quotient to connected components is locally path-connected when the ambient
space is locally path-connected. -/
instance instLocallyPathConnectedSpaceConnectedComponentsFiber [LocallyPathConnectedSpace X]
    (C : ConnectedComponents X) :
    LocallyPathConnectedSpace (ConnectedComponents.mk ⁻¹' {C} : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [connectedComponents_preimage_singleton, ← pathComponent_eq_connectedComponent]
  infer_instance

/-- **A locally connected space is the disjoint union of its connected components.**

The summand indexed by `C : ConnectedComponents X` is the fibre of the canonical quotient map
over `C`, so this decomposition does not require choosing representatives. -/
noncomputable def connectedComponentsSigmaHomeomorph [LocallyConnectedSpace X] :
    (Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) ≃ₜ X := by
  let e : (Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) ≃ X :=
    Equiv.sigmaPreimageEquiv ConnectedComponents.mk
  exact e.toHomeomorphOfContinuousOpen
    (continuous_sigma fun _ ↦ continuous_subtype_val)
    (isOpenMap_sigma.mpr fun C ↦
      ((isOpen_discrete {C}).preimage ConnectedComponents.continuous_coe).isOpenMap_subtype_val)

@[simp]
theorem connectedComponentsSigmaHomeomorph_apply [LocallyConnectedSpace X]
    (z : Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) :
    connectedComponentsSigmaHomeomorph z = z.2 :=
  (rfl)

@[simp]
theorem connectedComponentsSigmaHomeomorph_symm_apply [LocallyConnectedSpace X] (x : X) :
    connectedComponentsSigmaHomeomorph.symm x =
      ⟨ConnectedComponents.mk x, ⟨x, Set.mem_singleton _⟩⟩ :=
  (rfl)

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
