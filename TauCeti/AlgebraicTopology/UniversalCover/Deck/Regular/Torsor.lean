/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected.Torsor
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular.Basic

/-!
# Fibres of regular connected covers as deck torsors

For a preconnected covering map with regular deck action, evaluation at any point of a fibre
identifies the deck group with that fibre. This file packages the same fact in the standard
Mathlib language of torsors: the fibre is a principal homogeneous space for the deck group.

The torsor structure is bookkeeping needed by the universal-covers roadmap Stage 2, where
pointed covers and unpointed covers differ by changing a chosen lift of the basepoint, and
regular covers are characterized by transitivity of the deck action on fibres.

## Main declarations

* `TauCeti.Deck.fiberTorsor`: the regular-cover specialization.
* `TauCeti.Deck.fiber_sdiv_eq_deckEquivFiber_symm`: fibre division is the unique deck
  transformation carrying the second point to the first.

## References

This supplies a small prerequisite for the regular-cover and pointed/unpointed-cover
bookkeeping in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2. It specializes the local
torsor API in `TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected.Torsor` using the
regular deck-action API in `TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular.Basic`.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {b : B}

/-- The fibre of a regular preconnected covering is a torsor for its deck group. -/
@[reducible]
noncomputable def fiberTorsor [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hreg : IsRegular p) (b : B) :
    Torsor (Deck p) (p ⁻¹' {b}) := by
  letI := hreg.nonempty_fiber b
  letI := hreg.fiber_isPretransitive b
  exact fiberTorsorOfPretransitive hp b

/-- In the regular-cover fibre torsor, `e₁ /ₛ e₂` is the inverse equivalence from `e₂`
applied to `e₁`. -/
lemma fiber_sdiv_eq_deckEquivFiber_symm [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e₁ e₂ : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    e₁ /ₛ e₂ = (deckEquivFiber hp hreg e₂).symm e₁ :=
by
  letI := hreg.nonempty_fiber b
  letI := hreg.fiber_isPretransitive b
  exact fiber_sdiv_eq_deckEquivFiberOfSurjective_symm hp e₁ e₂

/-- In the regular-cover fibre torsor, the inverse of `deckEquivFiber` computes the quotient
of a point by the chosen base point. -/
@[simp]
lemma deckEquivFiber_symm_eq_sdiv [PreconnectedSpace E] (hp : IsCoveringMap p)
    (hreg : IsRegular p) (e e' : p ⁻¹' {b}) :
    letI := fiberTorsor hp hreg b
    (deckEquivFiber hp hreg e).symm e' = e' /ₛ e := by
  rw [fiber_sdiv_eq_deckEquivFiber_symm hp hreg]

end Deck

end TauCeti
