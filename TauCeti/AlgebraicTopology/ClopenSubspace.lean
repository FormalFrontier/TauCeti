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
# The homotopy theory of a clopen subspace

A subset `s` of a topological space `X` which is both open and closed absorbs every path and
every path homotopy that touches it: the domain of such a map is preconnected, so its image is
a preconnected set meeting the clopen set `s`, hence contained in `s`. Consequently the inclusion
`↥s → X` is an isomorphism on fundamental groups at every basepoint of `s`, and semilocal simple
connectivity is inherited by `↥s`.

The motivating instance is the path component of a point in a locally path connected space, which
is clopen by `IsClopen.pathComponent`. The universal-cover development assumes throughout that its
base is path connected; the results here supply the three standing hypotheses for the path
component of an arbitrary point of a locally path connected, semilocally simply connected space,
so that the whole theory applies to a base which is not path connected. See
`TauCeti/AlgebraicTopology/UniversalCover/PathComponent.lean` for that application.

## Main declarations

* `TauCeti.forall_mem_of_isClopen`: a continuous map out of a preconnected space which takes one
  value in a clopen set takes every value there.
* `TauCeti.homotopic_of_map_subtypeVal_homotopic`: path homotopy in `X` between two paths of a
  clopen subspace is already a path homotopy in the subspace.
* `TauCeti.fundamentalGroupMulEquivOfIsClopen`: the inclusion of a clopen subspace induces an
  isomorphism of fundamental groups.
* `TauCeti.fundamentalGroupMulEquivOfIsClopen_symm_fromPath`: its inverse corestricts a loop to
  the clopen subspace.
* `TauCeti.semilocallySimplyConnectedSpace_of_isClopen`: a clopen subspace of a semilocally
  simply connected space is semilocally simply connected.
* Instances making `↥(pathComponent x₀)` path connected, locally path connected and semilocally
  simply connected, and `TauCeti.fundamentalGroupMulEquivPathComponent` identifying its
  fundamental group with that of `X`.

## References

This supplies the "or one builds the cover of `pathComponent x₀`" clause of the standing
hypotheses in `TauCetiRoadmap/UniversalCovers/README.md`.
-/

public section

open scoped unitInterval
open Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- A continuous map from a preconnected space which takes one value in a clopen set `s` takes
every value in `s`: its range is preconnected and meets `s`. -/
theorem forall_mem_of_isClopen {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (hs : IsClopen s) {f : A → X} (hf : Continuous f) {a₀ : A} (h₀ : f a₀ ∈ s) (a : A) :
    f a ∈ s :=
  (isPreconnected_range hf).subset_isClopen hs ⟨f a₀, ⟨a₀, rfl⟩, h₀⟩ ⟨a, rfl⟩

/-- A path whose source lies in a clopen set stays in that set. -/
theorem forall_mem_of_isClopen_of_source_mem (hs : IsClopen s) {a b : X} (γ : Path a b)
    (ha : a ∈ s) (t : I) : γ t ∈ s :=
  forall_mem_of_isClopen hs γ.continuous (a₀ := 0) (by rw [γ.source]; exact ha) t

/-- Pushing the constant path at a point of a subspace forward along the inclusion gives the
constant path at the underlying point. -/
@[simp]
theorem map_subtypeVal_refl (a : s) :
    (Path.refl a).map (continuous_subtype_val (p := (· ∈ s))) = Path.refl (a : X) := by
  ext t
  rfl

/-- **Path homotopy reflects along the inclusion of a clopen subspace.** Two paths in a clopen
subspace `s` which become homotopic in the ambient space are already homotopic in `s`: the
homotopy is a continuous map out of the preconnected square `I × I` whose value at one corner
lies in `s`, so all of its values do. -/
theorem homotopic_of_map_subtypeVal_homotopic (hs : IsClopen s) {a b : s} {γ δ : Path a b}
    (h : (γ.map continuous_subtype_val).Homotopic (δ.map continuous_subtype_val)) :
    γ.Homotopic δ := by
  obtain ⟨H⟩ := h
  have hmem : ∀ p : I × I, H p ∈ s := fun p =>
    forall_mem_of_isClopen hs H.continuous (a₀ := (0, 0)) (by rw [H.source]; exact a.2) p
  refine Path.homotopic_of_continuous_square (fun p => ⟨H p, hmem p⟩)
    (H.continuous.subtype_mk hmem) (fun t => Subtype.ext ?_) (fun t => Subtype.ext ?_)
    (fun t => Subtype.ext ?_) (fun t => Subtype.ext ?_) <;> simp

/-- A loop in a clopen subspace which is null-homotopic in the ambient space is already
null-homotopic in the subspace. -/
theorem homotopic_refl_of_map_subtypeVal_homotopic_refl (hs : IsClopen s) {a : s} {γ : Path a a}
    (h : (γ.map continuous_subtype_val).Homotopic (Path.refl (a : X))) :
    γ.Homotopic (Path.refl a) :=
  homotopic_of_map_subtypeVal_homotopic hs (by rwa [map_subtypeVal_refl])

/-- The inclusion of a clopen subspace induces a bijection on fundamental groups. Surjectivity
is that a loop at a point of `s` never leaves `s`, injectivity that a null-homotopy of such a
loop never leaves `s` either. -/
theorem fundamentalGroup_map_subtypeVal_bijective (hs : IsClopen s) (a : s) :
    Function.Bijective
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)) a) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath g)
    have hnull : (γ.map continuous_subtype_val).Homotopic (Path.refl (a : X)) := by
      refine (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mp ?_
      exact (FundamentalGroup.map_fromPath
          (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)) a γ).symm.trans
        (hg.trans (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (a : X))))
    exact (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mpr
      (homotopic_refl_of_map_subtypeVal_homotopic_refl hs hnull)
  · intro g
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath g)
    refine ⟨FundamentalGroup.fromPath
      ⟦Path.codRestrict (x := a) (y := a) γ (forall_mem_of_isClopen_of_source_mem hs γ a.2)⟧, ?_⟩
    rw [FundamentalGroup.map_fromPath, Path.map_codRestrict]

/-- **A clopen subspace has the fundamental group of the ambient space.** The inclusion
`↥s → X` of a clopen subspace induces an isomorphism `π₁(s, a) ≃* π₁(X, a)`. -/
noncomputable def fundamentalGroupMulEquivOfIsClopen (hs : IsClopen s) (a : s) :
    FundamentalGroup s a ≃* FundamentalGroup X (a : X) :=
  MulEquiv.ofBijective _ (fundamentalGroup_map_subtypeVal_bijective hs a)

@[simp]
theorem fundamentalGroupMulEquivOfIsClopen_apply (hs : IsClopen s) (a : s)
    (g : FundamentalGroup s a) :
    fundamentalGroupMulEquivOfIsClopen hs a g =
      FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)) a g :=
  (rfl)

/-- The inverse isomorphism is computed by corestricting a loop of `X` to the clopen subspace it
cannot leave. -/
theorem fundamentalGroupMulEquivOfIsClopen_symm_fromPath (hs : IsClopen s) (a : s)
    (γ : Path (a : X) (a : X)) :
    (fundamentalGroupMulEquivOfIsClopen hs a).symm (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦Path.codRestrict (x := a) (y := a) γ
        (forall_mem_of_isClopen_of_source_mem hs γ a.2)⟧ := by
  rw [MulEquiv.symm_apply_eq, fundamentalGroupMulEquivOfIsClopen_apply,
    FundamentalGroup.map_fromPath, Path.map_codRestrict]
  rfl

/-- A clopen subspace of a semilocally simply connected space is semilocally simply connected:
the witnessing neighbourhood of a point pulls back, and a null-homotopy of a loop in the
subspace cannot leave it. -/
theorem semilocallySimplyConnectedSpace_of_isClopen [SemilocallySimplyConnectedSpace X]
    (hs : IsClopen s) : SemilocallySimplyConnectedSpace s where
  exists_mem_nhds_loops_nullhomotopic a := by
    obtain ⟨U, hU, hloop⟩ :=
      SemilocallySimplyConnectedSpace.exists_mem_nhds_loops_nullhomotopic (a : X)
    refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.tendsto a hU, fun γ hγ => ?_⟩
    exact homotopic_refl_of_map_subtypeVal_homotopic_refl hs
      (hloop (γ.map continuous_subtype_val) (by simpa using hγ))

section PathComponent

variable (x₀ : X)

/-- The path component of a point, as a subspace, is path connected. -/
instance instPathConnectedSpaceSubtypePathComponent :
    PathConnectedSpace (pathComponent x₀) :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent

/-- In a locally path connected space the path components are open, hence locally path connected
as subspaces. -/
instance instLocallyPathConnectedSpaceSubtypePathComponent [LocallyPathConnectedSpace X] :
    LocallyPathConnectedSpace (pathComponent x₀) :=
  (IsOpen.pathComponent x₀).locallyPathConnectedSpace

/-- In a locally path connected space the path components are clopen, so they inherit semilocal
simple connectivity. -/
instance instSemilocallySimplyConnectedSpaceSubtypePathComponent [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    SemilocallySimplyConnectedSpace (pathComponent x₀) :=
  semilocallySimplyConnectedSpace_of_isClopen (IsClopen.pathComponent x₀)

/-- The basepoint of `X`, viewed as a point of its own path component. -/
abbrev pathComponentSelf : (pathComponent x₀ : Set X) :=
  ⟨x₀, mem_pathComponent_self x₀⟩

@[simp] theorem pathComponentSelf_coe : (pathComponentSelf x₀ : X) = x₀ := (rfl)

/-- **The path component of `x₀` carries the fundamental group of `X` at `x₀`.** Loops at `x₀`
and their homotopies never leave the path component. -/
@[expose] noncomputable def fundamentalGroupMulEquivPathComponent :
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
      obtain ⟨H⟩ := hnull
      have hγmem : ∀ t, (γ.map continuous_subtype_val) t ∈ pathComponent x₀ := fun t =>
        ⟨Path.initialSegmentFamily (γ.map continuous_subtype_val) t⟩
      have hmem : ∀ p : I × I, H p ∈ pathComponent x₀ := fun p =>
        Joined.mem_pathComponent
          ⟨Path.initialSegmentFamily (H.evalAt p.2) p.1⟩
          (H.map_zero_left p.2 ▸ hγmem p.2)
      refine Path.homotopic_of_continuous_square (fun p => ⟨H p, hmem p⟩)
        (H.continuous.subtype_mk hmem) (fun t => Subtype.ext ?_) (fun t => Subtype.ext ?_)
        (fun t => Subtype.ext ?_) (fun t => Subtype.ext ?_) <;> simp
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
  rfl

/-- The inverse path-component equivalence corestricts a representative loop to the path
component, which contains each of its initial segments. -/
@[simp]
theorem fundamentalGroupMulEquivPathComponent_symm_fromPath (γ : Path x₀ x₀) :
    (fundamentalGroupMulEquivPathComponent x₀).symm (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath
        ⟦Path.codRestrict (x := pathComponentSelf x₀) (y := pathComponentSelf x₀) γ
          (fun t => ⟨Path.initialSegmentFamily γ t⟩)⟧ := by
  rw [MulEquiv.symm_apply_eq, fundamentalGroupMulEquivPathComponent_apply,
    FundamentalGroup.map_fromPath]
  change Path.Homotopic.Quotient.mk γ =
    Path.Homotopic.Quotient.mk
      ((Path.codRestrict (x := pathComponentSelf x₀) (y := pathComponentSelf x₀) γ
        (fun t => ⟨Path.initialSegmentFamily γ t⟩)).map continuous_subtype_val)
  exact congrArg Path.Homotopic.Quotient.mk
    (Path.map_codRestrict (s := pathComponent x₀) (x := pathComponentSelf x₀)
      (y := pathComponentSelf x₀) γ
      (fun t => show γ t ∈ pathComponent x₀ from ⟨Path.initialSegmentFamily γ t⟩)).symm

end PathComponent

end TauCeti
