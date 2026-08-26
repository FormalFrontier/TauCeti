/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.PathComponent
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.UniversalCover
public import TauCeti.Topology.Covering.Clopen

/-!
# The universal cover of a path component

The universal-cover development assumes that the base is path connected, so that the endpoint
projection is surjective. Dropping that assumption, based paths out of `x₀` still only see the
path component of `x₀`, and the roadmap's standing hypotheses accordingly allow building the
cover of `pathComponent x₀` instead. This file does that.

For `X` locally path connected and semilocally simply connected — but *not* assumed path
connected — the path component of `x₀` inherits all three standing hypotheses
(`TauCeti/AlgebraicTopology/PathComponent.lean`). Its universal cover is therefore
available, and because the subspace is clopen the composite of its endpoint projection with the
inclusion is a covering map of `X` itself, with range exactly `pathComponent x₀`. Total-space
path connectedness and simple connectivity are inherited from the universal cover, being
statements about the same topological space.

The deck group is unchanged by the corestriction, so the identification of `π₁` on a clopen
subspace turns the universal cover's deck computation into a statement about `X`: the deck group
of the path-component cover is `(π₁(X, x₀))ᵐᵒᵖ`, the same opposite-group convention pinned in
`TauCeti.UniversalCover.deckFundamentalGroupEquiv`.

## Main declarations

* `TauCeti.PathComponentCover`: the universal cover of the path component of `x₀`.
* `TauCeti.pathComponentCoverProj`: its projection down to `X`.
* `TauCeti.isCoveringMap_pathComponentCoverProj` and
  `TauCeti.range_pathComponentCoverProj`: it is a covering map of `X` with range the path
  component of `x₀`.
* `TauCeti.existsUnique_continuousMap_lifts_pathComponent`: the universal lifting property,
  stated for maps into `X`.
* `TauCeti.deckPathComponentCoverProjEquiv`: its deck group is `(π₁(X, x₀))ᵐᵒᵖ`.

## References

This is the "or one builds the cover of `pathComponent x₀`" clause of the standing hypotheses of
`TauCetiRoadmap/UniversalCovers/README.md`, the one case its Stage 0 hypotheses exclude rather
than handle.
-/

public section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- The universal cover of the path component of `x₀`. Its three standing hypotheses hold
because the path component is a clopen subspace of `X`; no path connectedness of `X` itself is
needed. -/
abbrev PathComponentCover : Type _ := UniversalCover (pathComponentSelf x₀)

/-- The projection of the universal cover of the path component of `x₀` down to `X`, the endpoint
projection followed by the inclusion of the path component. -/
abbrev pathComponentCoverProj : PathComponentCover x₀ → X :=
  Subtype.val ∘ UniversalCover.proj

/-- **The universal cover of a path component covers the whole space.** The path component is
clopen, so the missing fibres over the other path components are evenly covered by empty
trivialisations. -/
theorem isCoveringMap_pathComponentCoverProj : IsCoveringMap (pathComponentCoverProj x₀) :=
  isCoveringMap_subtypeVal_comp (IsClopen.pathComponent x₀)
    (UniversalCover.isCoveringMap (pathComponentSelf x₀))

omit [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
/-- The image of the path-component cover is exactly the path component of `x₀`. -/
theorem range_pathComponentCoverProj :
    Set.range (pathComponentCoverProj x₀) = pathComponent x₀ :=
  (UniversalCover.proj_surjective.range_comp Subtype.val).trans Subtype.range_coe

/-- **Universal property of the path-component cover.** A continuous map into `X` from a path
connected, locally path connected, simply connected space lifts uniquely once the image of one
point is prescribed. Path connectedness of the source is what confines its image to a single
path component of `X`, so no hypothesis on the values of `f` is required beyond the one implicit
in `he`. -/
theorem existsUnique_continuousMap_lifts_pathComponent {A : Type*} [TopologicalSpace A]
    [LocallyPathConnectedSpace A] [SimplyConnectedSpace A] (f : C(A, X))
    (a₀ : A) (e₀ : PathComponentCover x₀) (he : pathComponentCoverProj x₀ e₀ = f a₀) :
    ∃! F : C(A, PathComponentCover x₀),
      F a₀ = e₀ ∧ pathComponentCoverProj x₀ ∘ F = f := by
  have hmem : ∀ a, f a ∈ pathComponent x₀ := fun a =>
    Joined.mem_pathComponent ⟨(PathConnectedSpace.somePath a₀ a).map f.continuous⟩
      (he ▸ (UniversalCover.proj e₀).2)
  refine (existsUnique_congr fun F => and_congr_right fun _ => ?_).mp
    (UniversalCover.existsUnique_continuousMap_lifts (pathComponentSelf x₀)
      ⟨fun a => ⟨f a, hmem a⟩, by fun_prop⟩ a₀ e₀ (Subtype.ext he))
  refine ⟨fun h => funext fun a => congrArg Subtype.val (congrFun h a),
    fun h => funext fun a => Subtype.ext (congrFun h a)⟩

omit [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
/-- Corestricting the endpoint projection to the path component does not change its deck
group. -/
theorem deck_pathComponentCoverProj :
    Deck (pathComponentCoverProj x₀) =
      Deck (UniversalCover.proj : PathComponentCover x₀ → (pathComponent x₀ : Set X)) :=
  deck_subtypeVal_comp _

/-- **The deck group of the path-component cover is the opposite fundamental group of `X`.**
The corestriction leaves the deck group alone, the universal cover of the path component has
deck group the opposite of the fundamental group of that path component, and a clopen subspace
has the fundamental group of the ambient space. -/
noncomputable def deckPathComponentCoverProjEquiv :
    Deck (pathComponentCoverProj x₀) ≃* (FundamentalGroup X x₀)ᵐᵒᵖ :=
  (MulEquiv.subgroupCongr (deck_pathComponentCoverProj x₀)).trans <|
    (UniversalCover.deckFundamentalGroupEquiv (pathComponentSelf x₀)).trans <|
      MulEquiv.op (fundamentalGroupMulEquivPathComponent x₀)

private theorem deckPathComponentCoverProjEquiv_symm_op_eq (g : FundamentalGroup X x₀) :
    (deckPathComponentCoverProjEquiv x₀).symm (MulOpposite.op g) =
      (MulEquiv.subgroupCongr (deck_pathComponentCoverProj x₀)).symm
        ((UniversalCover.deckFundamentalGroupEquiv (pathComponentSelf x₀)).symm
          (MulOpposite.op ((fundamentalGroupMulEquivPathComponent x₀).symm g))) := by
  rw [deckPathComponentCoverProjEquiv]
  rfl

/-- The inverse deck-group equivalence sends `op g` to the loop deck transformation associated
to the inverse of the corresponding loop in the path component. -/
@[simp]
theorem deckPathComponentCoverProjEquiv_symm_op (g : FundamentalGroup X x₀) :
    (deckPathComponentCoverProjEquiv x₀).symm (MulOpposite.op g) =
      (MulEquiv.subgroupCongr (deck_pathComponentCoverProj x₀)).symm
        (UniversalCover.loopDeck (pathComponentSelf x₀)
          ((fundamentalGroupMulEquivPathComponent x₀).symm g)⁻¹) := by
  rw [deckPathComponentCoverProjEquiv_symm_op_eq,
    UniversalCover.deckFundamentalGroupEquiv_symm_op]

end TauCeti
