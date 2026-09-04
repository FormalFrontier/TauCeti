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
# Disjoint double-transposition terms vanish

The square of a grid differential is a sum over pairs of composable rectangles, and the
juxtaposition argument for `∂ ∘ ∂ = 0` splits those pairs according to how many side columns the
two rectangles have in common. Both columns in common is the annular case of `Annulus.lean`, where
the second rectangle returns to the source of the first. This file treats the opposite extreme,
for the fully blocked and the unblocked differential alike: the target state is obtained from the
source by two *disjoint* column transpositions.

That configuration is exactly the disjoint-side case of the case split in `SideOverlap.lean`. Two
disjoint column transpositions move four columns, whereas two transpositions sharing a column move
only three, so every two-step decomposition of such a target has disjoint pairs of side columns.
Reordering the two rectangle moves, `GridRectangleDecomposition.commute`, is then an involution on
the decompositions the unblocked differential counts. Exchanging the two toroidal domains
preserves `X`-avoidance and the weight `V^{O(r)}`. Emptiness is transferred separately by
`isEmpty_commute_first` and `isEmpty_commute_second`, using the cyclic-separation lemma
`Grid.mem_cIoo_and_mem_cIoo_swap_of_notMem`. Reordering also changes the intermediate state, so
it has no fixed point. In characteristic two the paired terms cancel.

The shared bookkeeping in `Count.lean` first reindexes the two-step terms as a single sum
over the finite set of decompositions both of whose rectangles the unblocked differential counts.
That reindexing holds for every pair of grid states and coefficient ring, so it serves the
intermediate case of two rectangles sharing exactly one side column,
`GridRectangleDecomposition.HasOneCommonSide`, just as well.

## Main results

The following results are in the `TauCeti.GridDiagram` namespace.

* `fullyBlockedDifferential_sq_single_apply_swapColumns_swapColumns_eq_zero_of_disjoint`: the
  fully blocked differential-square entry for two disjoint column transpositions vanishes.
* `unblockedDecompositionWeight_commute`: commuting a disjoint-side
  decomposition preserves its unblocked weight.
* `commute_mem_unblockedDecompositions_iff` and `commute_mem_fullyBlockedDecompositions_iff`:
  commuting preserves whether the unblocked, respectively fully blocked, differential counts a
  decomposition.
* `sum_unblockedCoefficient_mul_unblockedCoefficient_swapColumns_swapColumns_eq_zero_of_disjoint`:
  the weighted sum for two disjoint column transpositions vanishes in characteristic two.
* `unblockedDifferential_sq_single_apply_swapColumns_swapColumns_eq_zero_of_disjoint`: in
  characteristic two, that entry vanishes when the target is the source with two disjoint column
  transpositions applied.

## References

The argument follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
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

/-- Reordering a two-step decomposition with disjoint side columns preserves whether the fully
blocked differential counts it: both rectangles stay empty and the two domains, hence the covered
squares, are merely exchanged.

This is not a `simp` lemma: `mem_fullyBlockedDecompositions`, `mem_fullyBlockedRectangles` and
`commute_first_toGridRectangle`/`commute_second_toGridRectangle` are all `@[simp]`, so the
left-hand side is never in simp-normal form. -/
theorem commute_mem_fullyBlockedDecompositions_iff {x z : GridState n}
    (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    D.commute h ∈ G.fullyBlockedDecompositions x z ↔
      D ∈ G.fullyBlockedDecompositions x z := by
  have hforward : ∀ (E : GridRectangleDecomposition x z) (hE : E.HasDisjointSides),
      E ∈ G.fullyBlockedDecompositions x z → E.commute hE ∈ G.fullyBlockedDecompositions x z := by
    intro E hE hmem
    rw [G.mem_fullyBlockedDecompositions] at hmem ⊢
    refine ⟨?_, ?_⟩
    · rw [G.mem_fullyBlockedRectangles]
      exact ⟨E.isEmpty_commute_first hE
          (G.isEmpty_of_mem_fullyBlockedRectangles x E.middle hmem.1)
          (G.isEmpty_of_mem_fullyBlockedRectangles E.middle z hmem.2),
        (E.avoidsMarkings_commute_first_iff hE G).mpr
          (G.avoidsMarkings_of_mem_fullyBlockedRectangles E.middle z hmem.2)⟩
    · rw [G.mem_fullyBlockedRectangles]
      exact ⟨E.isEmpty_commute_second hE
          (G.isEmpty_of_mem_fullyBlockedRectangles x E.middle hmem.1)
          (G.isEmpty_of_mem_fullyBlockedRectangles E.middle z hmem.2),
        (E.avoidsMarkings_commute_second_iff hE G).mpr
          (G.avoidsMarkings_of_mem_fullyBlockedRectangles x E.middle hmem.1)⟩
  constructor
  · intro hD
    simpa only [D.commute_commute h] using
      hforward (D.commute h) (D.hasDisjointSides_commute h) hD
  · exact hforward D h

/-- The square of the fully blocked grid differential has zero matrix entry between a grid state
and the state obtained from it by two disjoint column transpositions.

This is the disjoint clause of the juxtaposition case analysis for the fully blocked complex. -/
theorem fullyBlockedDifferential_sq_single_apply_swapColumns_swapColumns_eq_zero_of_disjoint
    (x : GridState n) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hdisjoint : Disjoint ({a, b} : Finset (Fin n)) {c, d}) :
    G.fullyBlockedDifferential
        (G.fullyBlockedDifferential (Finsupp.single x (1 : ZMod 2)))
      ((x.swapColumns a b).swapColumns c d) = 0 := by
  -- Every fully blocked decomposition of such a target has disjoint side columns, and commuting
  -- its two rectangles preserves emptiness and marking avoidance without a fixed point, so the
  -- decomposition set has even cardinality.
  rw [G.fullyBlockedDifferential_sq_single_apply_eq_decompositionCount,
    G.fullyBlockedDecompositionCount_def]
  have hsum :
      ∑ D ∈ G.fullyBlockedDecompositions x
          ((x.swapColumns a b).swapColumns c d), (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution
      (fun D _ => D.commute (GridRectangleDecomposition.hasDisjointSides_of_disjoint x hab hcd
        hdisjoint D)) (fun _ _ => CharTwo.add_self_eq_zero 1) (fun D _ _ => D.commute_ne _)
      (fun D hD => (G.commute_mem_fullyBlockedDecompositions_iff D _).mpr hD)
      (fun D _ => D.commute_commute _)
  simpa using hsum

variable [CharP R 2]

/-- In characteristic two, the two-step matrix entry of the square of the unblocked differential
between a grid state and the state obtained from it by two disjoint column transpositions
vanishes.

This is the sum-level form of the disjoint case, and the form the remaining one-common-side case
will consume. -/
theorem
    sum_unblockedCoefficient_mul_unblockedCoefficient_swapColumns_swapColumns_eq_zero_of_disjoint
    (x : GridState n) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hdisjoint : Disjoint ({a, b} : Finset (Fin n)) {c, d}) :
    ∑ y : GridState n, G.unblockedCoefficient R x y *
        G.unblockedCoefficient R y ((x.swapColumns a b).swapColumns c d) = 0 := by
  -- Every two-step decomposition of such a target has disjoint pairs of side columns, so
  -- reordering the two rectangle moves is a weight-preserving involution on the counted
  -- decompositions with no fixed point.
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

Among the targets obtained from a grid state by two column transpositions, this leaves only the
case of two transpositions sharing exactly one column: two transpositions on the same pair of
columns return to the source, whose entry vanishes by the diagonal case in `Annulus.lean`. -/
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
