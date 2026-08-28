/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
public import TauCeti.Topology.PathComponent

/-!
# The algebraic topology of a path component

Loops and path homotopies based in `pathComponent x₀` remain there. Consequently, when the
ambient space is semilocally simply connected, the path component inherits semilocal simple
connectivity, and its inclusion into the ambient space induces an isomorphism on fundamental
groups at every point of the component.

## Main declarations

* An instance making `↥(pathComponent x₀)` semilocally simply connected.
* `FundamentalGroup.pathComponentMulEquiv`: the inclusion of `pathComponent x₀`
  induces an isomorphism of fundamental groups at any point of the component.
* `FundamentalGroup.pathComponentMulEquiv_symm_fromPath`: the inverse corestricts a loop
  to its path component.

## References

This supplies algebraic-topology prerequisites for the "or one builds the cover of
`pathComponent x₀`" clause in `TauCetiRoadmap/UniversalCovers/README.md`.
-/

public section

open scoped unitInterval
open Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

/-- A path component inherits semilocal simple connectivity: an ambient null-homotopy based in
the component remains in that component. -/
instance instSemilocallySimplyConnectedSpaceSubtypePathComponent
    [SemilocallySimplyConnectedSpace X] :
    SemilocallySimplyConnectedSpace (pathComponent x₀) :=
  ⟨fun a => by
    obtain ⟨U, hU, hloop⟩ :=
      SemilocallySimplyConnectedSpace.exists_mem_nhds_loops_nullhomotopic (a : X)
    refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.tendsto a hU, fun γ hγ => ?_⟩
    apply homotopic_pathComponent_of_map_subtypeVal_homotopic x₀
    rw [Path.map_refl]
    exact hloop (γ.map continuous_subtype_val) (by simpa using hγ)⟩

/-- **The path component of `x₀` carries the ambient fundamental group at each of its
points.** Loops at such a point and their homotopies never leave the path component. -/
noncomputable def _root_.FundamentalGroup.pathComponentMulEquiv (a : pathComponent x₀) :
    FundamentalGroup (pathComponent x₀) a ≃* FundamentalGroup X (a : X) :=
  MulEquiv.ofBijective
    (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x₀, X)) a) <| by
    constructor
    · rw [injective_iff_map_eq_one]
      intro g hg
      obtain ⟨γ, rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath g)
      have hnull : (γ.map continuous_subtype_val).Homotopic (Path.refl (a : X)) := by
        refine (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mp ?_
        exact (FundamentalGroup.map_fromPath
            (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x₀, X)) a γ).symm.trans
          (hg.trans (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (a : X))))
      refine (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mpr ?_
      apply homotopic_pathComponent_of_map_subtypeVal_homotopic x₀
      rw [Path.map_refl]
      exact hnull
    · intro g
      obtain ⟨γ, rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath g)
      have hmem : ∀ t, γ t ∈ pathComponent x₀ := γ.mem_pathComponent_of_mem a.2
      refine ⟨FundamentalGroup.fromPath
        ⟦Path.codRestrict (x := a) (y := a) γ hmem⟧, ?_⟩
      rw [FundamentalGroup.map_fromPath, Path.map_codRestrict]
      rfl

@[simp]
theorem _root_.FundamentalGroup.pathComponentMulEquiv_apply (a : pathComponent x₀)
    (g : FundamentalGroup (pathComponent x₀) a) :
    FundamentalGroup.pathComponentMulEquiv x₀ a g =
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x₀, X)) a g :=
  MulEquiv.ofBijective_apply _ _ g

/-- The inverse path-component equivalence corestricts a representative loop to the path
component containing its basepoint. -/
@[simp]
theorem _root_.FundamentalGroup.pathComponentMulEquiv_symm_fromPath (a : pathComponent x₀)
    (γ : Path (a : X) (a : X)) :
    (FundamentalGroup.pathComponentMulEquiv x₀ a).symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (Path.codRestrict (x := a) (y := a) γ (γ.mem_pathComponent_of_mem a.2))) := by
  rw [MulEquiv.symm_apply_eq, FundamentalGroup.pathComponentMulEquiv_apply]
  exact congrArg FundamentalGroup.fromPath <| congrArg Path.Homotopic.Quotient.mk <|
    (Path.map_codRestrict (s := pathComponent x₀) (x := a) (y := a) γ
      (γ.mem_pathComponent_of_mem a.2)).symm

end TauCeti
