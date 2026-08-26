/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
public import TauCeti.Topology.Homotopy.Path

/-!
# The homotopy theory of a path component

Paths and path homotopies based at `x₀` remain in `pathComponent x₀`, without any local
path-connectedness assumption. Consequently, when the ambient space is semilocally simply
connected, the path component inherits semilocal simple connectivity, and its inclusion into the
ambient space induces an isomorphism on fundamental groups. Under local path connectedness it also
inherits local path connectedness, supplying the three standing hypotheses needed by the
universal-cover construction.

## Main declarations

* Instances making `↥(pathComponent x₀)` path connected, locally path connected and semilocally
  simply connected.
* `TauCeti.fundamentalGroupMulEquivPathComponent`: the inclusion of `pathComponent x₀` induces
  an isomorphism of fundamental groups.
* `TauCeti.fundamentalGroupMulEquivPathComponent_symm_fromPath`: the inverse corestricts a loop to
  its path component.

## References

This supplies the "or one builds the cover of `pathComponent x₀`" clause of the standing
hypotheses in `TauCetiRoadmap/UniversalCovers/README.md`.
-/

public section

open scoped unitInterval
open Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

/-- Two paths in a path component which are homotopic in the ambient space are already
homotopic in the path component. -/
theorem homotopic_of_map_subtypeVal_homotopic_pathComponent
    {a b : pathComponent x₀} {γ δ : Path a b}
    (h : (γ.map continuous_subtype_val).Homotopic
      (δ.map continuous_subtype_val)) :
    γ.Homotopic δ := by
  obtain ⟨H⟩ := h
  have hγmem : ∀ t, (γ.map continuous_subtype_val) t ∈ pathComponent x₀ := fun t =>
    (γ t).2
  have hmem : ∀ p : I × I, H p ∈ pathComponent x₀ := fun p =>
    Joined.mem_pathComponent
      ⟨Path.initialSegmentFamily (H.evalAt p.2) p.1⟩
      (H.map_zero_left p.2 ▸ hγmem p.2)
  exact Path.homotopic_of_continuous_square (fun p => ⟨H p, hmem p⟩)
    (H.continuous.subtype_mk hmem) (fun t => Subtype.ext (H.map_zero_left t))
    (fun t => Subtype.ext (H.map_one_left t)) (fun t => Subtype.ext (H.source t))
    (fun t => Subtype.ext (H.target t))

/-- The path component of a point, as a subspace, is path connected. -/
instance instPathConnectedSpaceSubtypePathComponent :
    PathConnectedSpace (pathComponent x₀) :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent

/-- In a locally path connected space the path components are open, hence locally path connected
as subspaces. -/
instance instLocallyPathConnectedSpaceSubtypePathComponent [LocallyPathConnectedSpace X] :
    LocallyPathConnectedSpace (pathComponent x₀) :=
  (IsOpen.pathComponent x₀).locallyPathConnectedSpace

/-- A path component inherits semilocal simple connectivity: an ambient null-homotopy based in
the component remains in that component. -/
instance instSemilocallySimplyConnectedSpaceSubtypePathComponent
    [SemilocallySimplyConnectedSpace X] :
    SemilocallySimplyConnectedSpace (pathComponent x₀) :=
  ⟨fun a => by
    obtain ⟨U, hU, hloop⟩ :=
      SemilocallySimplyConnectedSpace.exists_mem_nhds_loops_nullhomotopic (a : X)
    refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.tendsto a hU, fun γ hγ => ?_⟩
    apply homotopic_of_map_subtypeVal_homotopic_pathComponent x₀
    rw [show (Path.refl a).map continuous_subtype_val = Path.refl (a : X) by rfl]
    exact hloop (γ.map continuous_subtype_val) (by simpa using hγ)⟩

/-- The basepoint of `X`, viewed as a point of its own path component. -/
abbrev pathComponentSelf : (pathComponent x₀ : Set X) :=
  ⟨x₀, mem_pathComponent_self x₀⟩

@[simp] theorem pathComponentSelf_coe : (pathComponentSelf x₀ : X) = x₀ := (rfl)

/-- **The path component of `x₀` carries the fundamental group of `X` at `x₀`.** Loops at `x₀`
and their homotopies never leave the path component. -/
noncomputable def fundamentalGroupMulEquivPathComponent :
    FundamentalGroup (pathComponent x₀) (pathComponentSelf x₀) ≃* FundamentalGroup X x₀ :=
  MulEquiv.ofBijective
    (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x₀, X))
      (pathComponentSelf x₀)) <| by
    constructor
    · rw [injective_iff_map_eq_one]
      intro g hg
      obtain ⟨γ, rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath g)
      have hnull : (γ.map continuous_subtype_val).Homotopic (Path.refl x₀) := by
        refine (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mp ?_
        exact (FundamentalGroup.map_fromPath
            (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x₀, X))
            (pathComponentSelf x₀) γ).symm.trans
          (hg.trans (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk x₀)))
      refine (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mpr ?_
      apply homotopic_of_map_subtypeVal_homotopic_pathComponent x₀
      rw [show (Path.refl (pathComponentSelf x₀)).map continuous_subtype_val =
        Path.refl x₀ by rfl]
      exact hnull
    · intro g
      obtain ⟨γ, rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath g)
      let hmem : ∀ t, γ t ∈ pathComponent x₀ := fun t => ⟨Path.initialSegmentFamily γ t⟩
      refine ⟨FundamentalGroup.fromPath
        ⟦Path.codRestrict (x := pathComponentSelf x₀) (y := pathComponentSelf x₀)
          γ hmem⟧, ?_⟩
      rw [FundamentalGroup.map_fromPath, Path.map_codRestrict]
      rfl

@[simp]
theorem fundamentalGroupMulEquivPathComponent_apply
    (g : FundamentalGroup (pathComponent x₀) (pathComponentSelf x₀)) :
    fundamentalGroupMulEquivPathComponent x₀ g =
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x₀, X))
        (pathComponentSelf x₀) g :=
  MulEquiv.ofBijective_apply _ _ g

/-- The inverse path-component equivalence corestricts a representative loop to the path
component, which contains each of its initial segments. -/
@[simp]
theorem fundamentalGroupMulEquivPathComponent_symm_fromPath (γ : Path x₀ x₀) :
    (fundamentalGroupMulEquivPathComponent x₀).symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (Path.codRestrict (x := pathComponentSelf x₀) (y := pathComponentSelf x₀) γ
            (fun t => ⟨Path.initialSegmentFamily γ t⟩))) := by
  rw [MulEquiv.symm_apply_eq, fundamentalGroupMulEquivPathComponent_apply]
  exact congrArg FundamentalGroup.fromPath <| congrArg Path.Homotopic.Quotient.mk <|
    (Path.map_codRestrict (s := pathComponent x₀) (x := pathComponentSelf x₀)
      (y := pathComponentSelf x₀) γ (fun t => ⟨Path.initialSegmentFamily γ t⟩)).symm

end TauCeti
