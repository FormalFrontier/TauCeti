/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.Normalizer

/-!
# The deck group of the cover attached to a subgroup

For `H ≤ π₁(X, x₀)`, the orbit quotient `UniversalCover x₀ / H` is a covering space of `X`
through `UniversalCover.subgroupQuotientProj`. This file computes its deck transformation
group:

  `Deck (subgroupQuotientProj x₀ H) ≃* N(H) ⧸ H`,

and, when `H` is normal, `Deck (subgroupQuotientProj x₀ H) ≃* π₁(X, x₀) ⧸ H`. Both are the
specialisation to the universal cover of
`TauCeti.Deck.IsQuotientCoveringMap.normalizerQuotientDeckMulEquiv`.

The isomorphism is stated for the left action of `π₁(X, x₀)` on the universal cover, in which
a loop class acts by prepending its inverse; this is the same convention as
`TauCeti.Deck.IsQuotientCoveringMap.deckMulEquiv`, and it is why no `ᵐᵒᵖ` appears here, unlike
in the monodromy identification `UniversalCover.deckFundamentalGroupEquiv`.

Taking `H = ⊥` recovers the deck group of the universal cover itself; taking `H` normal and
`H = ⊥` gives `π₁(X, x₀)` again.

## Main declarations

* `TauCeti.UniversalCover.deckSubgroupQuotientProjEquiv`: **the deck group of the cover
  attached to `H` is `N(H) ⧸ H`.**
* `TauCeti.UniversalCover.deckSubgroupQuotientProjEquivOfNormal`: for normal `H` this reads
  `π₁(X, x₀) ⧸ H`.

## References

This completes the deck-group half of Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`. It consumes the based-path universal cover
adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292), Mathlib's
quotient-covering-map interface due to Junyan Xu, and the covering-map property of
`subgroupQuotientProj` proved in
`TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence`.
-/

public section
noncomputable section

variable {X : Type*} [TopologicalSpace X]

namespace TauCeti.UniversalCover

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
variable (x₀ : X) (H : Subgroup (FundamentalGroup X x₀))

/-- **The deck group of the cover attached to `H ≤ π₁(X, x₀)` is the normalizer quotient
`N(H) ⧸ H`.** A normalizer class acts by descending its translation of the universal cover. -/
def deckSubgroupQuotientProjEquiv :
    (Subgroup.normalizer (H : Set (FundamentalGroup X x₀))) ⧸
        H.subgroupOf (Subgroup.normalizer (H : Set (FundamentalGroup X x₀)))
      ≃* Deck (subgroupQuotientProj x₀ H) :=
  Deck.IsQuotientCoveringMap.normalizerQuotientDeckMulEquiv
    (isQuotientCoveringMap (x₀ := x₀)) (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
    (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H)
    (isCoveringMap_subgroupQuotientProj x₀ H)

/-- The normalizer class of `g` acts on the cover attached to `H` by sending the class of `e`
to the class of `g • e`. -/
@[simp]
theorem deckSubgroupQuotientProjEquiv_mk_apply
    (g : Subgroup.normalizer (H : Set (FundamentalGroup X x₀))) (e : UniversalCover x₀) :
    (deckSubgroupQuotientProjEquiv x₀ H (QuotientGroup.mk g)).1 (Quotient.mk'' e) =
      Quotient.mk'' ((g : FundamentalGroup X x₀) • e) := by
  simpa [deckSubgroupQuotientProjEquiv] using
    Deck.IsQuotientCoveringMap.normalizerDeckHom_apply
      (isQuotientCoveringMap (x₀ := x₀)) (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
      (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) g e

/-- The inverse of the deck transformation attached to the normalizer class of `g` sends the
class of `e` to the class of `g⁻¹ • e`. -/
@[simp]
theorem deckSubgroupQuotientProjEquiv_mk_symm_apply
    (g : Subgroup.normalizer (H : Set (FundamentalGroup X x₀))) (e : UniversalCover x₀) :
    (deckSubgroupQuotientProjEquiv x₀ H (QuotientGroup.mk g)).1.symm (Quotient.mk'' e) =
      Quotient.mk'' ((g : FundamentalGroup X x₀)⁻¹ • e) := by
  simpa [deckSubgroupQuotientProjEquiv] using
    Deck.IsQuotientCoveringMap.normalizerDeckHom_symm_apply
      (isQuotientCoveringMap (x₀ := x₀)) (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
      (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) g e

/-- **For a normal subgroup `H ◁ π₁(X, x₀)`, the deck group of the cover attached to `H` is
`π₁(X, x₀) ⧸ H`**, so that cover is regular. -/
def deckSubgroupQuotientProjEquivOfNormal [H.Normal] :
    FundamentalGroup X x₀ ⧸ H ≃* Deck (subgroupQuotientProj x₀ H) :=
  Deck.IsQuotientCoveringMap.quotientDeckMulEquivOfNormal
    (isQuotientCoveringMap (x₀ := x₀)) (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
    (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H)
    (isCoveringMap_subgroupQuotientProj x₀ H)

/-- For normal `H`, the class of `g` acts on the cover attached to `H` by sending the class of
`e` to the class of `g • e`. -/
@[simp]
theorem deckSubgroupQuotientProjEquivOfNormal_mk_apply [H.Normal]
    (g : FundamentalGroup X x₀) (e : UniversalCover x₀) :
    (deckSubgroupQuotientProjEquivOfNormal x₀ H (QuotientGroup.mk g)).1
        (Quotient.mk'' e) = Quotient.mk'' (g • e) := by
  simpa [deckSubgroupQuotientProjEquivOfNormal] using
    Deck.IsQuotientCoveringMap.deckHomOfNormal_apply
      (isQuotientCoveringMap (x₀ := x₀)) (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
      (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) g e

/-- For normal `H`, the inverse of the deck transformation attached to the class of `g` sends
the class of `e` to the class of `g⁻¹ • e`. -/
@[simp]
theorem deckSubgroupQuotientProjEquivOfNormal_mk_symm_apply [H.Normal]
    (g : FundamentalGroup X x₀) (e : UniversalCover x₀) :
    (deckSubgroupQuotientProjEquivOfNormal x₀ H (QuotientGroup.mk g)).1.symm
        (Quotient.mk'' e) = Quotient.mk'' (g⁻¹ • e) := by
  simpa [deckSubgroupQuotientProjEquivOfNormal] using
    Deck.IsQuotientCoveringMap.deckHomOfNormal_symm_apply
      (isQuotientCoveringMap (x₀ := x₀)) (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
      (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H) g e

end TauCeti.UniversalCover
