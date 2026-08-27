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
connected — the path component of `x₀` is path connected, is open and therefore locally path
connected, and absorbs ambient null-homotopies, so it inherits all three standing hypotheses
(`TauCeti/AlgebraicTopology/PathComponent.lean`). Its universal cover is therefore available,
and because the subspace is clopen the composite of its endpoint projection with the inclusion
is a covering map of `X` itself, with range exactly `pathComponent x₀`. Total-space path
connectedness and simple connectivity are inherited from the universal cover, being statements
about the same topological space.

The deck group is unchanged by the inclusion, and
`FundamentalGroup.pathComponentMulEquiv` identifies the fundamental group of the path
component with that of `X` at the same point. Thus the deck group of the path-component cover is
`(π₁(X, x₀))ᵐᵒᵖ`, with the same opposite-group convention pinned in
`TauCeti.UniversalCover.deckFundamentalGroupEquiv`.

## Main declarations

* `TauCeti.UniversalCover.PathComponentCover`: the universal cover of the path component of `x₀`.
* `TauCeti.UniversalCover.pathComponentCoverProj`: its projection down to `X`.
* `TauCeti.UniversalCover.isCoveringMap_pathComponentCoverProj` and
  `TauCeti.UniversalCover.range_pathComponentCoverProj`: it is a covering map of `X` with range
  the path component of `x₀`.
* `TauCeti.UniversalCover.existsUnique_continuousMap_lifts_pathComponentCoverProj`: the universal
  lifting property, stated for maps into `X`.
* `TauCeti.UniversalCover.deckPathComponentFundamentalGroupEquiv`: its deck group is
  `(π₁(X, x₀))ᵐᵒᵖ`.

## References

This is the "or one builds the cover of `pathComponent x₀`" clause of the standing hypotheses of
`TauCetiRoadmap/UniversalCovers/README.md`, the one case its Stage 0 hypotheses exclude rather
than handle. It consumes the based-path universal cover adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292) and the deck group
adapted from Kim Morrison's
[mathlib4#40135](https://github.com/leanprover-community/mathlib4/pull/40135).
-/

public section

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- The universal cover of the path component of `x₀`. The component is path connected; local
path connectedness follows from its openness, and semilocal simple connectivity follows because
ambient null-homotopies based in the component remain there. -/
abbrev PathComponentCover : Type _ := UniversalCover (pathComponentSelf x₀)

/-- The projection of the universal cover of the path component of `x₀` down to `X`, the endpoint
projection followed by the inclusion of the path component. -/
abbrev pathComponentCoverProj : PathComponentCover x₀ → X :=
  Subtype.val ∘ UniversalCover.proj

/-- **The universal cover of a path component is a covering map into the ambient space.** The path
component is clopen, so fibres over the other path components are empty and evenly covered by
empty trivialisations. -/
theorem isCoveringMap_pathComponentCoverProj : IsCoveringMap (pathComponentCoverProj x₀) :=
  (UniversalCover.isCoveringMap (pathComponentSelf x₀)).subtypeVal_comp (IsClopen.pathComponent x₀)

omit [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
/-- The image of the path-component cover is exactly the path component of `x₀`. -/
theorem range_pathComponentCoverProj :
    Set.range (pathComponentCoverProj x₀) = pathComponent x₀ :=
  (UniversalCover.proj_surjective.range_comp Subtype.val).trans Subtype.range_coe

/-- **Universal property of the path-component cover.** A continuous map into `X` from a locally
path connected, simply connected space lifts uniquely once the image of one point is prescribed.
-/
theorem existsUnique_continuousMap_lifts_pathComponentCoverProj {A : Type*} [TopologicalSpace A]
    [LocallyPathConnectedSpace A] [SimplyConnectedSpace A] (f : C(A, X))
    (a₀ : A) (e₀ : PathComponentCover x₀) (he : pathComponentCoverProj x₀ e₀ = f a₀) :
    ∃! F : C(A, PathComponentCover x₀),
      F a₀ = e₀ ∧ pathComponentCoverProj x₀ ∘ F = f :=
  (isCoveringMap_pathComponentCoverProj x₀).existsUnique_continuousMap_lifts f a₀ e₀ he

omit [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
/-- Postcomposing the endpoint projection with the path-component inclusion does not change its
deck group. -/
theorem deck_pathComponentCoverProj :
    Deck (pathComponentCoverProj x₀) =
      Deck (UniversalCover.proj : PathComponentCover x₀ → (pathComponent x₀ : Set X)) :=
  deck_comp_of_injective Subtype.val_injective _

/-- **The deck group of the path-component cover is the opposite fundamental group of `X`.**
The inclusion leaves the deck group unchanged, the universal cover of the component has deck
group the opposite of its fundamental group, and
`FundamentalGroup.pathComponentMulEquiv` identifies that group with `π₁(X, x₀)`. -/
noncomputable def deckPathComponentFundamentalGroupEquiv :
    Deck (pathComponentCoverProj x₀) ≃* (FundamentalGroup X x₀)ᵐᵒᵖ :=
  (MulEquiv.subgroupCongr (deck_pathComponentCoverProj x₀)).trans <|
    (UniversalCover.deckFundamentalGroupEquiv (pathComponentSelf x₀)).trans <|
      MulEquiv.op (FundamentalGroup.pathComponentMulEquiv x₀ (pathComponentSelf x₀))

/-- The inverse of an opposite equivalence acts on an `op` by the opposite of the inverse. -/
private theorem mulEquiv_op_symm_apply_op {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : H) : (MulEquiv.op e).symm (MulOpposite.op h) =
      MulOpposite.op (e.symm h) :=
  rfl

/-- The inverse deck-group equivalence sends `op g` to the loop deck transformation associated
to the inverse of the corresponding loop in the path component. -/
@[simp]
theorem deckPathComponentFundamentalGroupEquiv_symm_op (g : FundamentalGroup X x₀) :
    (deckPathComponentFundamentalGroupEquiv x₀).symm (MulOpposite.op g) =
      (MulEquiv.subgroupCongr (deck_pathComponentCoverProj x₀)).symm
        (UniversalCover.loopDeck (pathComponentSelf x₀)
          ((FundamentalGroup.pathComponentMulEquiv x₀ (pathComponentSelf x₀)).symm g)⁻¹) := by
  rw [deckPathComponentFundamentalGroupEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.symm_trans_apply, mulEquiv_op_symm_apply_op,
    UniversalCover.deckFundamentalGroupEquiv_symm_op]

end TauCeti.UniversalCover
