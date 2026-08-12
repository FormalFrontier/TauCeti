/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.NoetherianSpace
public import TauCeti.Topology.ConnectedComponents

/-!
# Connected components of Noetherian spaces

A Noetherian topological space has only finitely many connected components. Indeed, it has
finitely many irreducible components, every irreducible set lies in one connected component,
and the irreducible components cover the space. Consequently the quotient by connected
components is a finite discrete space, and every connected component is open as well as closed.

## Main declarations

* `TauCeti.finite_connectedComponents_of_finite_irreducibleComponents`: finiteness of the
  irreducible components implies finiteness of the connected components.
* `TauCeti.finite_connectedComponents_of_noetherianSpace`: a Noetherian space has finitely
  many connected components.
* `TauCeti.instLocallyConnectedSpaceOfNoetherianSpace`: a Noetherian space is locally
  connected.

## References

* The Stacks Project, Tag 0052, *Noetherian topological spaces*.

The finite-component conclusion is used for the identity-component and component-group
milestone in Layer 3 of the ReductiveGroups roadmap. Applied to the spectrum of a finite-type
coordinate algebra, it supplies the finiteness input for the construction of `π₀`.
-/

public section

open Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

namespace TauCeti

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

/-- A Noetherian space has finitely many connected components. -/
theorem finite_connectedComponents_of_noetherianSpace [TopologicalSpace.NoetherianSpace X] :
    Finite (ConnectedComponents X) :=
  finite_connectedComponents_of_finite_irreducibleComponents
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- A Noetherian space is locally connected. In particular, each connected component is
clopen. -/
instance instLocallyConnectedSpaceOfNoetherianSpace [TopologicalSpace.NoetherianSpace X] :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro U hU x hx
  let _ : TopologicalSpace.NoetherianSpace U := TopologicalSpace.NoetherianSpace.set U
  let _ : Finite (ConnectedComponents U) := finite_connectedComponents_of_noetherianSpace
  have hopen : IsOpen (connectedComponent (⟨x, hx⟩ : U)) := by
    rw [← connectedComponents_preimage_singleton]
    exact (isOpen_discrete
      ({((⟨x, hx⟩ : U) : ConnectedComponents U)} : Set (ConnectedComponents U))).preimage
        ConnectedComponents.continuous_coe
  rw [connectedComponentIn_eq_image hx]
  exact hU.isOpenEmbedding_subtypeVal.isOpenMap _ hopen

end TauCeti
