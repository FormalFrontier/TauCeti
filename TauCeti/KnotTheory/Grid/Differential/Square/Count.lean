/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Coefficient
public import TauCeti.KnotTheory.Grid.Differential.Square.Decomposition
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# Counting two-rectangle decompositions

The coefficient of the square of the fully blocked grid differential is a sum over intermediate
states of products of rectangle counts. This file identifies that expression with the parity of a
single finite set: the set of pairs of composable fully blocked empty rectangles with prescribed
source and target.

This is the algebraic handoff needed by the juxtaposition proof of `∂² = 0`. Its geometric part can
now act directly on `GridDiagram.fullyBlockedDecompositions G x z`: a fixed-point-free involution
of this finite set proves that its cardinality is even, and hence that the corresponding
coefficient of the differential square vanishes.

The same shared decomposition construction also reindexes the matrix entries of the unblocked
differential square as weighted sums over pairs of empty, `X`-avoiding rectangles. This is the
counting form used by the disjoint and one-common-side cases.

*Which region carries a marking.* Every fully blocked statement below is relative to the ambient
`GridDiagram.fullyBlockedRectangles`, and none of them unfolds the marking condition: they relate
two objects assembled from that one finite set. The marking region is fixed upstream by
`GridRectangle.AvoidsMarkings`, which asks that no square a rectangle covers carry an `O` or an
`X` marking.

## Main definitions

* `TauCeti.GridDiagram.fullyBlockedDecompositions`: composable pairs of fully blocked empty
  rectangles with fixed endpoints.
* `TauCeti.GridDiagram.fullyBlockedDecompositionCount`: the cardinality of this set modulo two.
* `TauCeti.GridDiagram.unblockedDecompositions`: composable pairs of rectangles counted by the
  unblocked differential.
* `TauCeti.GridDiagram.unblockedDecompositionWeight`: the product of their two monomial weights.

## Main results

* `TauCeti.GridDiagram.mem_fullyBlockedDecompositions`: membership means that both rectangles in
  the decomposition are fully blocked.
* `TauCeti.GridDiagram.card_fullyBlockedDecompositions`: the cardinality is the sum, over
  intermediate states, of the product of the two rectangle-set cardinalities.
* `TauCeti.GridDiagram.fullyBlockedDecompositionCount_eq_sum`: the parity count is the coefficient
  sum appearing in the square of the differential.
* `TauCeti.GridDiagram.fullyBlockedDecompositionCount_eq_zero_iff_even`: its vanishing is exactly
  evenness of the finite decomposition set.
* `TauCeti.GridDiagram.fullyBlockedDifferential_comp_self_eq_zero_iff_decompositionCount`: the
  differential squares to zero exactly when every decomposition count vanishes.
* `TauCeti.GridDiagram.sum_unblockedCoefficient_mul_unblockedCoefficient`: an unblocked two-step
  matrix entry is the weighted sum over the corresponding decompositions.

## References

This supplies the counting step for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane
G.3, "The complexes and `∂² = 0`". The pairing of juxtaposed empty rectangles follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (x z : GridState n)

/-- The finite set of decompositions from `x` to `z` in which both constituent rectangles are
fully blocked and empty for the grid diagram `G`.

The intermediate state is retained as part of `GridRectangleDecomposition`; it is determined by
the first rectangle, but is the index over which the differential-square coefficient is summed. -/
noncomputable def fullyBlockedDecompositions :
    Finset (GridRectangleDecomposition x z) :=
  GridRectangleDecomposition.decompositionsOf G.fullyBlockedRectangles x z

/-- A decomposition is fully blocked exactly when each of its two rectangles belongs to the
corresponding fully blocked rectangle set. -/
@[simp]
theorem mem_fullyBlockedDecompositions (D : GridRectangleDecomposition x z) :
    D ∈ G.fullyBlockedDecompositions x z ↔
      D.first ∈ G.fullyBlockedRectangles x D.middle ∧
        D.second ∈ G.fullyBlockedRectangles D.middle z := by
  classical
  simp [fullyBlockedDecompositions]

/-! ### The unblocked differential -/

/-- The two-step rectangle decompositions from `x` to `z` both of whose rectangles the unblocked
differential counts: both are empty and cover no `X`-marking. -/
noncomputable def unblockedDecompositions : Finset (GridRectangleDecomposition x z) :=
  GridRectangleDecomposition.decompositionsOf G.unblockedRectangles x z

/-- A two-step decomposition is counted by the unblocked differential exactly when each of its
two rectangles is. -/
@[simp]
theorem mem_unblockedDecompositions (D : GridRectangleDecomposition x z) :
    D ∈ G.unblockedDecompositions x z ↔
      D.first ∈ G.unblockedRectangles x D.middle ∧
        D.second ∈ G.unblockedRectangles D.middle z := by
  classical
  simp [unblockedDecompositions]

section

variable (R : Type*) [CommSemiring R]

/-- The weight of a two-step rectangle decomposition in the square of the unblocked differential:
the product of the weights `V^{O(r)}` of its two rectangles. -/
noncomputable def unblockedDecompositionWeight {x z : GridState n}
    (D : GridRectangleDecomposition x z) :
    MvPolynomial (Fin n) R :=
  G.OMonomial R D.first.toGridRectangle * G.OMonomial R D.second.toGridRectangle

/-- The unblocked decomposition weight is the product of the monomial weights of its two
rectangles. -/
@[simp]
theorem unblockedDecompositionWeight_def {x z : GridState n}
    (D : GridRectangleDecomposition x z) :
    G.unblockedDecompositionWeight R D =
      G.OMonomial R D.first.toGridRectangle * G.OMonomial R D.second.toGridRectangle := by
  rw [unblockedDecompositionWeight]

/-- The two-step matrix entry of the square of the unblocked differential is the sum of the
weights of the two-step decompositions it counts. -/
theorem sum_unblockedCoefficient_mul_unblockedCoefficient (x z : GridState n) :
    ∑ y : GridState n, G.unblockedCoefficient R x y * G.unblockedCoefficient R y z =
      ∑ D ∈ G.unblockedDecompositions x z, G.unblockedDecompositionWeight R D := by
  have hstep : ∀ y : GridState n,
      G.unblockedCoefficient R x y * G.unblockedCoefficient R y z =
        ∑ r₁ ∈ G.unblockedRectangles x y, ∑ r₂ ∈ G.unblockedRectangles y z,
          G.OMonomial R r₁.toGridRectangle * G.OMonomial R r₂.toGridRectangle := fun y => by
    rw [G.unblockedCoefficient_def R x y, G.unblockedCoefficient_def R y z,
      Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hstep y]
  simp only [unblockedDecompositionWeight_def]
  exact (GridRectangleDecomposition.sum_decompositionsOf G.unblockedRectangles x z
    (fun _ r₁ r₂ =>
      G.OMonomial R r₁.toGridRectangle * G.OMonomial R r₂.toGridRectangle)).symm

end

/-! ### Fully blocked counts -/

/-- The first rectangle in a fully blocked decomposition is empty. -/
theorem isEmpty_first_of_mem_fullyBlockedDecompositions
    {D : GridRectangleDecomposition x z} (hD : D ∈ G.fullyBlockedDecompositions x z) :
    D.first.IsEmpty :=
  G.isEmpty_of_mem_fullyBlockedRectangles x D.middle
    ((G.mem_fullyBlockedDecompositions x z D).mp hD).1

/-- The second rectangle in a fully blocked decomposition is empty. -/
theorem isEmpty_second_of_mem_fullyBlockedDecompositions
    {D : GridRectangleDecomposition x z} (hD : D ∈ G.fullyBlockedDecompositions x z) :
    D.second.IsEmpty :=
  G.isEmpty_of_mem_fullyBlockedRectangles D.middle z
    ((G.mem_fullyBlockedDecompositions x z D).mp hD).2

/-- The first rectangle in a fully blocked decomposition avoids every marking. -/
theorem avoidsMarkings_first_of_mem_fullyBlockedDecompositions
    {D : GridRectangleDecomposition x z} (hD : D ∈ G.fullyBlockedDecompositions x z) :
    D.first.AvoidsMarkings G :=
  G.avoidsMarkings_of_mem_fullyBlockedRectangles x D.middle
    ((G.mem_fullyBlockedDecompositions x z D).mp hD).1

/-- The second rectangle in a fully blocked decomposition avoids every marking. -/
theorem avoidsMarkings_second_of_mem_fullyBlockedDecompositions
    {D : GridRectangleDecomposition x z} (hD : D ∈ G.fullyBlockedDecompositions x z) :
    D.second.AvoidsMarkings G :=
  G.avoidsMarkings_of_mem_fullyBlockedRectangles D.middle z
    ((G.mem_fullyBlockedDecompositions x z D).mp hD).2

/-- The number of fully blocked decompositions is the sum over intermediate states of the product
of the two rectangle-set cardinalities. -/
theorem card_fullyBlockedDecompositions :
    (G.fullyBlockedDecompositions x z).card =
      ∑ y : GridState n,
        (G.fullyBlockedRectangles x y).card * (G.fullyBlockedRectangles y z).card := by
  exact GridRectangleDecomposition.card_decompositionsOf G.fullyBlockedRectangles x z

/-- There are no fully blocked decompositions from `x` to a state outside the two-step
column-swap support of `x`. -/
theorem fullyBlockedDecompositions_eq_empty_of_notMem_twoStep
    (hz : z ∉ x.twoStepColumnSwapNeighbors) : G.fullyBlockedDecompositions x z = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr fun D _ =>
    hz D.target_mem_twoStepColumnSwapNeighbors

/-- The number modulo two of fully blocked two-rectangle decompositions from `x` to `z`. -/
noncomputable def fullyBlockedDecompositionCount : ZMod 2 :=
  (G.fullyBlockedDecompositions x z).card

/-- The fully blocked decomposition count is the cardinality of
`fullyBlockedDecompositions`, coerced to `ZMod 2`. -/
theorem fullyBlockedDecompositionCount_def :
    G.fullyBlockedDecompositionCount x z =
      ((G.fullyBlockedDecompositions x z).card : ZMod 2) :=
  (rfl)

/-- A fully blocked decomposition count vanishes exactly when the corresponding finite set has
even cardinality. This is the parity form consumed by a fixed-point-free pairing of
decompositions. -/
theorem fullyBlockedDecompositionCount_eq_zero_iff_even :
    G.fullyBlockedDecompositionCount x z = 0 ↔
      Even (G.fullyBlockedDecompositions x z).card := by
  rw [fullyBlockedDecompositionCount_def, ZMod.natCast_eq_zero_iff_even]

/-- The fully blocked decomposition count vanishes outside the two-step column-swap support. -/
theorem fullyBlockedDecompositionCount_eq_zero_of_notMem_twoStep
    (hz : z ∉ x.twoStepColumnSwapNeighbors) : G.fullyBlockedDecompositionCount x z = 0 := by
  rw [fullyBlockedDecompositionCount_def,
    G.fullyBlockedDecompositions_eq_empty_of_notMem_twoStep x z hz]
  simp

/-- The parity of fully blocked decompositions is the sum over intermediate states of the product
of the two fully blocked rectangle counts. -/
theorem fullyBlockedDecompositionCount_eq_sum :
    G.fullyBlockedDecompositionCount x z =
      ∑ y : GridState n, G.fullyBlockedRectangleCount x y *
        G.fullyBlockedRectangleCount y z := by
  rw [fullyBlockedDecompositionCount_def, G.card_fullyBlockedDecompositions x z]
  simp only [Nat.cast_sum, Nat.cast_mul, fullyBlockedRectangleCount_def]

/-- The coefficient of `z` in the square of the differential applied to the generator `x` is the
parity of the fully blocked decompositions from `x` to `z`. -/
theorem fullyBlockedDifferential_sq_single_apply_eq_decompositionCount :
    G.fullyBlockedDifferential
        (G.fullyBlockedDifferential (Finsupp.single x (1 : ZMod 2))) z =
      G.fullyBlockedDecompositionCount x z := by
  rw [fullyBlockedDifferential_apply_apply, fullyBlockedDifferential_single,
    G.fullyBlockedDifferential_sq_single_apply x z,
    G.fullyBlockedDecompositionCount_eq_sum x z]

/-- The fully blocked differential squares to zero exactly when every fully blocked
two-rectangle decomposition set has even cardinality. -/
theorem fullyBlockedDifferential_comp_self_eq_zero_iff_decompositionCount :
    G.fullyBlockedDifferential.comp G.fullyBlockedDifferential = 0 ↔
      ∀ x z : GridState n, G.fullyBlockedDecompositionCount x z = 0 := by
  rw [G.fullyBlockedDifferential_comp_self_eq_zero_iff]
  simp only [G.fullyBlockedDecompositionCount_eq_sum]

end GridDiagram

end TauCeti
