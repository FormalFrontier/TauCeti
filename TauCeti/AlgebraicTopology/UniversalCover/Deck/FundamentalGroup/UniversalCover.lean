/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.Opposite

/-!
# Deck transformations of the universal cover

For a path-connected, locally path-connected, semilocally simply connected space `X`, the
endpoint projection from the based-path universal cover is regular. Indeed, the explicit
fundamental-group action from `UniversalCover.Action` acts through deck transformations and is
transitive on each fibre.

Combining this regularity with the simple connectedness of the universal cover and the generic
regular-cover comparison gives the convention-correct form of the classical calculation

`Deck (UniversalCover.proj : UniversalCover x₀ → X) ≃* (FundamentalGroup X x₀)ᵐᵒᵖ`.

The opposite is genuine: the fundamental group acts on the universal cover by prepending the
inverse loop, while deck transformations are composed as homeomorphisms. This is the convention
pinned by `TauCeti.Deck.IsRegular.deckFundamentalGroupEquiv`.

## Main declarations

* `TauCeti.UniversalCover.loopDeck`: the deck transformation induced by a loop class.
* `TauCeti.UniversalCover.isRegular_proj`: regularity of the universal-cover projection.
* `TauCeti.UniversalCover.deckFundamentalGroupEquiv`: the deck group of the universal cover is
  the opposite fundamental group.

## References

This completes Stage 1, item 5 of `TauCetiRoadmap/UniversalCovers/README.md`. The construction
uses the universal-cover action adapted from Kim Morrison's mathlib4 PR
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292), and the generic
comparison ultimately uses Junyan Xu's `IsQuotientCoveringMap.fundamentalGroupEquiv` from
`Mathlib.Topology.Homotopy.Lifting`.
-/

public section
noncomputable section

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

/-- A loop class acts on the universal cover by a deck transformation of the endpoint
projection. -/
@[expose] def loopDeck (g : FundamentalGroup X x₀) :
    Deck (proj : UniversalCover x₀ → X) :=
  ⟨Homeomorph.smul g, fun p => proj_smul g p⟩

/-- The deck transformation induced by a loop class acts by the fundamental-group action. -/
@[simp]
lemma loopDeck_apply (g : FundamentalGroup X x₀) (p : UniversalCover x₀) :
    (loopDeck x₀ g).1 p = g • p :=
  rfl

/-- The identity loop class induces the identity deck transformation. -/
@[simp]
lemma loopDeck_one :
    loopDeck x₀ (CategoryTheory.CategoryStruct.id
      ({ as := x₀ } : FundamentalGroupoid X)) = 1 := by
  apply Subtype.ext
  apply Homeomorph.ext
  intro p
  rw [loopDeck_apply]
  exact one_smul _ _

/-- Multiplication of loop classes corresponds to composition of their deck transformations. -/
@[simp]
lemma loopDeck_mul (g h : FundamentalGroup X x₀) :
    loopDeck x₀ (CategoryTheory.CategoryStruct.comp h g) = loopDeck x₀ g * loopDeck x₀ h := by
  apply Subtype.ext
  apply Homeomorph.ext
  intro p
  exact mul_smul g h p

/-- The fundamental-group action, bundled as a homomorphism into the deck group of the
universal-cover projection. -/
@[expose] def loopDeckHom :
    FundamentalGroup X x₀ →* Deck (proj : UniversalCover x₀ → X) where
  toFun := loopDeck x₀
  map_one' := loopDeck_one x₀
  map_mul' := loopDeck_mul x₀

@[simp]
lemma loopDeckHom_apply (g : FundamentalGroup X x₀) :
    loopDeckHom x₀ g = loopDeck x₀ g :=
  rfl

/-- The endpoint projection of the universal cover has regular deck action. -/
theorem isRegular_proj [PathConnectedSpace X] :
    Deck.IsRegular (proj : UniversalCover x₀ → X) := by
  rw [Deck.isRegular_iff_exists_apply_eq]
  refine ⟨proj_surjective, ?_⟩
  intro p q hpq
  obtain ⟨g, hg⟩ := proj_eq_iff_mem_orbit.mp hpq
  refine ⟨loopDeck x₀ g⁻¹, ?_⟩
  rw [loopDeck_apply, ← hg, inv_smul_smul]

/-- The deck transformation group of the based-path universal cover is the opposite of the
fundamental group of the base. -/
noncomputable def deckFundamentalGroupEquiv
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    Deck (proj : UniversalCover x₀ → X) ≃* (FundamentalGroup X x₀)ᵐᵒᵖ :=
  (isRegular_proj x₀).deckFundamentalGroupEquiv (isCoveringMap x₀)
    ⟨mk x₀ (Path.Homotopic.Quotient.refl x₀), rfl⟩

/-- A deck transformation corresponds to a loop class exactly when the loop's monodromy moves
the canonical lift by that deck transformation. -/
lemma deckFundamentalGroupEquiv_apply_eq_op_iff
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X]
    (φ : Deck (proj : UniversalCover x₀ → X)) (g : FundamentalGroup X x₀) :
    deckFundamentalGroupEquiv x₀ φ = MulOpposite.op g ↔
      ((isCoveringMap x₀).monodromy g
        ⟨mk x₀ (Path.Homotopic.Quotient.refl x₀), rfl⟩ : UniversalCover x₀) =
        φ • mk x₀ (Path.Homotopic.Quotient.refl x₀) := by
  exact Deck.IsRegular.deckFundamentalGroupEquiv_apply_eq_op_iff
    (isRegular_proj x₀) (isCoveringMap x₀)
      ⟨mk x₀ (Path.Homotopic.Quotient.refl x₀), rfl⟩ φ g

end TauCeti.UniversalCover
