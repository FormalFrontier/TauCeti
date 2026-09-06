/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Decomposition
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# Repartitions of two-step grid rectangle domains

Two two-step grid rectangle decompositions are repartitions when the rectangles in each
decomposition cover disjoint sets of squares and the unions of those sets agree. This is the
domain relation used by the juxtaposition proof of `∂⁻ ∘ ∂⁻ = 0`: it transports multiplicative
weights and avoidance of marked squares without requiring the two cuts to be distinct.

## Main definitions

* `TauCeti.GridRectangleDecomposition.IsRepartition`: two decompositions partition the same set
  of covered squares.

## Main results

* `TauCeti.GridRectangleDecomposition.IsRepartition.prod_coveredSquares_mul_prod_coveredSquares`:
  a repartition preserves the product of any multiplicative weight on squares.
* `TauCeti.GridRectangleDecomposition.IsRepartition.OMonomial_mul_OMonomial`: a repartition
  preserves the product of the `O`-monomial weights of the unblocked differential.
* `TauCeti.GridRectangleDecomposition.IsRepartition.disjoint_coveredSquares_first`,
  `TauCeti.GridRectangleDecomposition.IsRepartition.disjoint_coveredSquares_second`: avoidance
  of a set of squares transfers across a repartition.

## References

This supplies the shared domain relation for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`".
The repartition argument follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- `E` is a repartition of `D`: the rectangles in each decomposition cover disjoint sets of
squares, and the two unions agree. -/
structure IsRepartition (D E : GridRectangleDecomposition x z) : Prop where
  /-- The two rectangles in the left-hand decomposition cover disjoint sets of squares. -/
  disjoint_coveredSquares_left :
    Disjoint D.first.toGridRectangle.coveredSquares D.second.toGridRectangle.coveredSquares
  /-- The two rectangles in the right-hand decomposition cover disjoint sets of squares. -/
  disjoint_coveredSquares_right :
    Disjoint E.first.toGridRectangle.coveredSquares E.second.toGridRectangle.coveredSquares
  /-- The two decompositions cover the same squares. -/
  coveredSquares_union_eq :
    E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares =
      D.first.toGridRectangle.coveredSquares ∪ D.second.toGridRectangle.coveredSquares

namespace IsRepartition

variable {D E : GridRectangleDecomposition x z}

/-- Being a repartition is a symmetric relation. -/
theorem symm (h : D.IsRepartition E) : E.IsRepartition D where
  disjoint_coveredSquares_left := h.disjoint_coveredSquares_right
  disjoint_coveredSquares_right := h.disjoint_coveredSquares_left
  coveredSquares_union_eq := h.coveredSquares_union_eq.symm

/-- A repartition preserves the product of any multiplicative weight on squares: both
decompositions partition the same finite set of covered squares. -/
theorem prod_coveredSquares_mul_prod_coveredSquares (h : D.IsRepartition E) {M : Type*}
    [CommMonoid M] (f : Fin n × Fin n → M) :
    (∏ p ∈ E.first.toGridRectangle.coveredSquares, f p) *
        ∏ p ∈ E.second.toGridRectangle.coveredSquares, f p =
      (∏ p ∈ D.first.toGridRectangle.coveredSquares, f p) *
        ∏ p ∈ D.second.toGridRectangle.coveredSquares, f p := by
  rw [← Finset.prod_union h.disjoint_coveredSquares_right, h.coveredSquares_union_eq,
    Finset.prod_union h.disjoint_coveredSquares_left]

/-- A repartition preserves the product of the `O`-monomial weights that the unblocked
differential attaches to its two rectangles. -/
theorem OMonomial_mul_OMonomial (h : D.IsRepartition E) (G : GridDiagram n) (R : Type*)
    [CommSemiring R] :
    G.OMonomial R E.first.toGridRectangle * G.OMonomial R E.second.toGridRectangle =
      G.OMonomial R D.first.toGridRectangle * G.OMonomial R D.second.toGridRectangle := by
  simp only [G.OMonomial_eq_prod_coveredSquares R]
  exact h.prod_coveredSquares_mul_prod_coveredSquares _

/-- If neither rectangle of the left-hand decomposition meets a set of squares, then the union
of the right-hand decomposition does not meet it either. -/
theorem disjoint_coveredSquares_union (h : D.IsRepartition E) {s : Finset (Fin n × Fin n)}
    (h₁ : Disjoint D.first.toGridRectangle.coveredSquares s)
    (h₂ : Disjoint D.second.toGridRectangle.coveredSquares s) :
    Disjoint (E.first.toGridRectangle.coveredSquares ∪
      E.second.toGridRectangle.coveredSquares) s := by
  rw [h.coveredSquares_union_eq]
  exact Finset.disjoint_union_left.mpr ⟨h₁, h₂⟩

/-- If neither rectangle of the left-hand decomposition meets a set of squares, then neither
does the first rectangle of the right-hand decomposition. -/
theorem disjoint_coveredSquares_first (h : D.IsRepartition E) {s : Finset (Fin n × Fin n)}
    (h₁ : Disjoint D.first.toGridRectangle.coveredSquares s)
    (h₂ : Disjoint D.second.toGridRectangle.coveredSquares s) :
    Disjoint E.first.toGridRectangle.coveredSquares s :=
  (Finset.disjoint_union_left.mp (h.disjoint_coveredSquares_union h₁ h₂)).1

/-- If neither rectangle of the left-hand decomposition meets a set of squares, then neither
does the second rectangle of the right-hand decomposition. -/
theorem disjoint_coveredSquares_second (h : D.IsRepartition E) {s : Finset (Fin n × Fin n)}
    (h₁ : Disjoint D.first.toGridRectangle.coveredSquares s)
    (h₂ : Disjoint D.second.toGridRectangle.coveredSquares s) :
    Disjoint E.second.toGridRectangle.coveredSquares s :=
  (Finset.disjoint_union_left.mp (h.disjoint_coveredSquares_union h₁ h₂)).2

end IsRepartition

end GridRectangleDecomposition

end TauCeti
