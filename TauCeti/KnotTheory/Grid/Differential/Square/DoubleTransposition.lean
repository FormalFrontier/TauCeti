/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.CharP.Two
public import TauCeti.KnotTheory.Grid.Differential.Square.Count
public import TauCeti.KnotTheory.Grid.Differential.Square.SideOverlap

/-!
# Disjoint double-transposition terms vanish in characteristic two

The square of the unblocked grid differential `∂⁻` of `Unblocked.lean` is a sum over pairs of
composable rectangles, and the juxtaposition argument for `∂⁻ ∘ ∂⁻ = 0` splits those pairs
according to how the two rectangles meet. `Annulus.lean` closed the annular case, where the second
rectangle returns to the source of the first. This file closes the opposite extreme: the target
state is obtained from the source by two *disjoint* column transpositions.

That configuration is exactly the disjoint-side case of the case split in `SideOverlap.lean`. Two
disjoint column transpositions move four columns, whereas two transpositions sharing a column move
only three, so every two-step decomposition of such a target has disjoint pairs of side columns.
Reordering the two rectangle moves, `GridRectangleDecomposition.commute`, is then an involution on
the decompositions the unblocked differential counts. Exchanging the two toroidal domains
preserves `X`-avoidance and the weight `V^{O(r)}`. Emptiness is transferred separately by
`isEmpty_commute_first` and `isEmpty_commute_second`, using the cyclic-separation lemma
`Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap`. Reordering also changes the intermediate state, so
it has no fixed point. In characteristic two the paired terms cancel.

The shared bookkeeping in `Count.lean` first reindexes the two-step terms as a single sum
over the finite set of decompositions both of whose rectangles the unblocked differential counts.
That reindexing holds for every pair of grid states and coefficient ring, and is also the entry
point for the remaining case: two rectangles sharing exactly one side column,
`GridRectangleDecomposition.HasOneCommonSide`.

## Main results

The following results are in the `TauCeti.GridDiagram` namespace.

* `unblockedDecompositionWeight_commute`: commuting a disjoint-side
  decomposition preserves its unblocked weight.
* `commute_mem_unblockedDecompositions_iff`: commuting preserves whether the
  unblocked differential counts a decomposition.
* `sum_unblockedCoefficient_mul_unblockedCoefficient_swapColumns_swapColumns_eq_zero_of_disjoint`:
  the weighted sum for two disjoint column transpositions vanishes in characteristic two.
* `unblockedDifferential_sq_single_apply_swapColumns_swapColumns_eq_zero_of_disjoint`: in
  characteristic two, that entry vanishes when the target is the source with two disjoint column
  transpositions applied.

## References

This supplies the disjoint-side case for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`",
specifically the "disjoint" clause of its juxtaposition case analysis. The argument follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- Reordering a two-step decomposition with disjoint side columns preserves its weight: the two
toroidal domains are exchanged. -/
theorem unblockedDecompositionWeight_commute {x z : GridState n}
    (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    G.unblockedDecompositionWeight R (D.commute h) =
      G.unblockedDecompositionWeight R D := by
  rw [G.unblockedDecompositionWeight_def R, G.unblockedDecompositionWeight_def R,
    D.commute_first_toGridRectangle h,
    D.commute_second_toGridRectangle h, mul_comm]

/-- Reordering a two-step decomposition with disjoint side columns preserves whether the
unblocked differential counts it: both rectangles stay empty and the two domains, hence the
covered squares, are merely exchanged.

This is not a `simp` lemma: `mem_unblockedDecompositions`, `mem_unblockedRectangles` and
`commute_first_toGridRectangle`/`commute_second_toGridRectangle` are all `@[simp]`, so the
left-hand side is never in simp-normal form. -/
theorem commute_mem_unblockedDecompositions_iff {x z : GridState n}
    (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    D.commute h ∈ G.unblockedDecompositions x z ↔
      D ∈ G.unblockedDecompositions x z := by
  have hforward : ∀ (E : GridRectangleDecomposition x z) (hE : E.HasDisjointSides),
      E ∈ G.unblockedDecompositions x z → E.commute hE ∈ G.unblockedDecompositions x z := by
    intro E hE hmem
    rw [G.mem_unblockedDecompositions x z E] at hmem
    obtain ⟨h₁, h₂⟩ := hmem
    refine (G.mem_unblockedDecompositions x z _).mpr ⟨?_, ?_⟩
    · rw [G.mem_unblockedRectangles]
      refine ⟨E.isEmpty_commute_first hE (G.isEmpty_of_mem_unblockedRectangles h₁)
        (G.isEmpty_of_mem_unblockedRectangles h₂), ?_⟩
      rw [E.commute_first_toGridRectangle hE]
      exact G.disjoint_XSet_of_mem_unblockedRectangles h₂
    · rw [G.mem_unblockedRectangles]
      refine ⟨E.isEmpty_commute_second hE (G.isEmpty_of_mem_unblockedRectangles h₁)
        (G.isEmpty_of_mem_unblockedRectangles h₂), ?_⟩
      rw [E.commute_second_toGridRectangle hE]
      exact G.disjoint_XSet_of_mem_unblockedRectangles h₁
  constructor
  · intro hD
    simpa only [D.commute_commute h] using
      hforward (D.commute h) (D.hasDisjointSides_commute h) hD
  · exact hforward D h

variable [CharP R 2]

/-- In characteristic two, the two-step matrix entry of the square of the unblocked differential
between a grid state and the state obtained from it by two disjoint column transpositions
vanishes.

Every two-step decomposition of such a target has disjoint pairs of side columns, so reordering
the two rectangle moves is a weight-preserving involution on the counted decompositions with no
fixed point. -/
theorem
    sum_unblockedCoefficient_mul_unblockedCoefficient_swapColumns_swapColumns_eq_zero_of_disjoint
    (x : GridState n) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hdisjoint : Disjoint ({a, b} : Finset (Fin n)) {c, d}) :
    ∑ y : GridState n, G.unblockedCoefficient R x y *
        G.unblockedCoefficient R y ((x.swapColumns a b).swapColumns c d) = 0 := by
  rw [G.sum_unblockedCoefficient_mul_unblockedCoefficient R]
  refine Finset.sum_involution
    (fun D _ => D.commute (GridRectangleDecomposition.hasDisjointSides_of_disjoint x hab hcd
      hdisjoint D)) (fun D _ => ?_) (fun D _ _ => D.commute_ne _) (fun D hD => ?_)
    (fun D _ => ?_)
  · rw [G.unblockedDecompositionWeight_commute R D]
    exact CharTwo.add_self_eq_zero _
  · exact (G.commute_mem_unblockedDecompositions_iff D _).mpr hD
  · exact D.commute_commute _

/-- In characteristic two, the square of the unblocked grid differential has zero matrix entry
between a grid state and the state obtained from it by two disjoint column transpositions.

Together with the vanishing of the diagonal entries in `Annulus.lean`, this leaves only the case
of two rectangles sharing exactly one side column. -/
theorem unblockedDifferential_sq_single_apply_swapColumns_swapColumns_eq_zero_of_disjoint
    (x : GridState n) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hdisjoint : Disjoint ({a, b} : Finset (Fin n)) {c, d}) :
    G.unblockedDifferential R (G.unblockedDifferential R (Finsupp.single x 1))
      ((x.swapColumns a b).swapColumns c d) = 0 := by
  rw [G.unblockedDifferential_sq_single_apply R x]
  exact
    G.sum_unblockedCoefficient_mul_unblockedCoefficient_swapColumns_swapColumns_eq_zero_of_disjoint
      R x hab hcd hdisjoint

end GridDiagram

end TauCeti
