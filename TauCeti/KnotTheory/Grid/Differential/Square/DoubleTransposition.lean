/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.CharP.Two
public import TauCeti.KnotTheory.Grid.Differential.Square.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.SideOverlap

/-!
# The double-transposition terms of the unblocked grid differential square vanish

The square of the unblocked grid differential `∂⁻` of `Unblocked.lean` is a sum over pairs of
composable rectangles, and the juxtaposition argument for `∂⁻ ∘ ∂⁻ = 0` splits those pairs
according to how the two rectangles meet. `Annulus.lean` closed the annular case, where the second
rectangle returns to the source of the first. This file closes the opposite extreme: the target
state is obtained from the source by two *disjoint* column transpositions.

That configuration is exactly the disjoint-side case of the case split in `SideOverlap.lean`. Two
disjoint column transpositions move four columns, whereas two transpositions sharing a column move
only three, so every two-step decomposition of such a target has disjoint pairs of side columns.
Reordering the two rectangle moves, `GridRectangleDecomposition.commute`, is then an involution on
the decompositions the unblocked differential counts: it exchanges the two toroidal domains, hence
preserves emptiness, `X`-avoidance and the weight `V^{O(r)}`, and it changes the intermediate
state, so it has no fixed point. In characteristic two the paired terms cancel.

The shared bookkeeping in `Decomposition.lean` first reindexes the two-step terms as a single sum
over the finite set of decompositions both of whose rectangles the unblocked differential counts.
That reindexing holds for every pair of grid states and coefficient ring, and is also the entry
point for the remaining case: two rectangles sharing exactly one side column,
`GridRectangleDecomposition.HasOneCommonSide`.

## Main results

* `TauCeti.GridRectangleDecomposition.hasDisjointSides_of_disjoint`: every two-step decomposition
  whose target is the source with two disjoint column transpositions applied has disjoint pairs of
  side columns.
* `TauCeti.GridDiagram.unblockedDifferential_sq_single_apply_eq_zero_of_disjoint`: in
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

namespace GridRectangleDecomposition

variable {n : ℕ}

/-- Two disjoint column transpositions move four columns, so no two-step rectangle decomposition
of the resulting state can share a side column.

The two rectangles of a decomposition fix every column outside their four side columns. Sharing a
side column would leave only three such columns, and sharing both would return to the source. -/
theorem hasDisjointSides_of_disjoint (x : GridState n) {a b c d : Fin n} (hab : a ≠ b)
    (hcd : c ≠ d) (hdisjoint : Disjoint ({a, b} : Finset (Fin n)) {c, d})
    (D : GridRectangleDecomposition x ((x.swapColumns a b).swapColumns c d)) :
    D.HasDisjointSides := by
  obtain ⟨hac, had⟩ : a ≠ c ∧ a ≠ d := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      Finset.disjoint_left.mp hdisjoint (by simp : a ∈ ({a, b} : Finset (Fin n)))
  obtain ⟨hbc, hbd⟩ : b ≠ c ∧ b ≠ d := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      Finset.disjoint_left.mp hdisjoint (by simp : b ∈ ({a, b} : Finset (Fin n)))
  -- the four columns the two transpositions move, and their images
  have hza : (x.swapColumns a b).swapColumns c d a = x b := by
    simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hac had]
  have hzb : (x.swapColumns a b).swapColumns c d b = x a := by
    simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hbc hbd]
  have hzc : (x.swapColumns a b).swapColumns c d c = x d := by
    simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
  have hzd : (x.swapColumns a b).swapColumns c d d = x c := by
    simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hmoved : ∀ e ∈ ({a, b, c, d} : Finset (Fin n)),
      e ∈ D.first.sideColumns ∪ D.second.sideColumns := by
    intro e he
    by_contra hnot
    rw [Finset.mem_union, not_or] at hnot
    have hfix := D.apply_eq_of_notMem_sideColumns hnot.1 hnot.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hab (x.toPerm.injective (hza ▸ hfix).symm)
    · exact hab (x.toPerm.injective (hzb ▸ hfix))
    · exact hcd (x.toPerm.injective (hzc ▸ hfix).symm)
    · exact hcd (x.toPerm.injective (hzd ▸ hfix))
  rcases D.hasDisjointSides_or_hasOneCommonSide_or_eq with hcase | hcase | hcase
  · exact hcase
  · exfalso
    have hinter : D.commonSideColumns = D.first.sideColumns ∩ D.second.sideColumns := by
      ext e
      simp
    have hcard : D.commonSideColumns.card = 1 := by
      rw [Finset.card_eq_one_iff_existsUnique]
      simp only [mem_commonSideColumns]
      exact D.hasOneCommonSide_iff_existsUnique.mp hcase
    have hsum := Finset.card_union_add_card_inter D.first.sideColumns D.second.sideColumns
    rw [D.first.card_sideColumns, D.second.card_sideColumns, ← hinter, hcard] at hsum
    have hfour : ({a, b, c, d} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]),
        Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
    have hle := Finset.card_le_card hmoved
    rw [hfour] at hle
    omega
  · exfalso
    have hxa : x a = x b := by rw [← hza, hcase]
    exact hab (x.toPerm.injective hxa)

end GridRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- Reordering a two-step decomposition with disjoint side columns preserves its weight: the two
toroidal domains are exchanged. -/
theorem decompositionWeight_commute {x z : GridState n}
    (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides) :
    G.decompositionWeight R (D.commute h) = G.decompositionWeight R D := by
  change G.OMonomial R (D.commute h).first.toGridRectangle *
      G.OMonomial R (D.commute h).second.toGridRectangle =
    G.OMonomial R D.first.toGridRectangle * G.OMonomial R D.second.toGridRectangle
  rw [D.commute_first_toGridRectangle h,
    D.commute_second_toGridRectangle h, mul_comm]

/-- Reordering a counted two-step decomposition with disjoint side columns gives another counted
decomposition: both rectangles stay empty and the two domains, hence the covered squares, are
merely exchanged. -/
theorem commute_mem_unblockedDecompositions {x z : GridState n}
    (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides)
    (hD : D ∈ G.unblockedDecompositions x z) :
    D.commute h ∈ G.unblockedDecompositions x z := by
  rw [G.mem_unblockedDecompositions D] at hD
  obtain ⟨h₁, h₂⟩ := hD
  refine (G.mem_unblockedDecompositions _).mpr ⟨?_, ?_⟩
  · rw [G.mem_unblockedRectangles]
    refine ⟨D.isEmpty_commute_first h (G.isEmpty_of_mem_unblockedRectangles h₁)
      (G.isEmpty_of_mem_unblockedRectangles h₂), ?_⟩
    rw [D.commute_first_toGridRectangle h]
    exact G.disjoint_XSet_of_mem_unblockedRectangles h₂
  · rw [G.mem_unblockedRectangles]
    refine ⟨D.isEmpty_commute_second h (G.isEmpty_of_mem_unblockedRectangles h₁)
      (G.isEmpty_of_mem_unblockedRectangles h₂), ?_⟩
    rw [D.commute_second_toGridRectangle h]
    exact G.disjoint_XSet_of_mem_unblockedRectangles h₁

variable [CharP R 2]

/-- In characteristic two, the two-step matrix entry of the square of the unblocked differential
between a grid state and the state obtained from it by two disjoint column transpositions
vanishes.

Every two-step decomposition of such a target has disjoint pairs of side columns, so reordering
the two rectangle moves is a weight-preserving involution on the counted decompositions with no
fixed point. -/
theorem sum_unblockedCoefficient_mul_unblockedCoefficient_eq_zero_of_disjoint
    (x : GridState n) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hdisjoint : Disjoint ({a, b} : Finset (Fin n)) {c, d}) :
    ∑ y : GridState n, G.unblockedCoefficient R x y *
        G.unblockedCoefficient R y ((x.swapColumns a b).swapColumns c d) = 0 := by
  rw [G.sum_unblockedCoefficient_mul_unblockedCoefficient R]
  refine Finset.sum_involution
    (fun D _ => D.commute (GridRectangleDecomposition.hasDisjointSides_of_disjoint x hab hcd
      hdisjoint D)) (fun D _ => ?_) (fun D _ _ => D.commute_ne _) (fun D hD => ?_)
    (fun D _ => ?_)
  · rw [G.decompositionWeight_commute R D]
    exact CharTwo.add_self_eq_zero _
  · exact G.commute_mem_unblockedDecompositions D _ hD
  · exact D.commute_commute _

/-- In characteristic two, the square of the unblocked grid differential has no matrix entry
between a grid state and the state obtained from it by two disjoint column transpositions.

Together with the vanishing of the diagonal entries in `Annulus.lean`, this leaves only the case
of two rectangles sharing exactly one side column. -/
theorem unblockedDifferential_sq_single_apply_eq_zero_of_disjoint
    (x : GridState n) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hdisjoint : Disjoint ({a, b} : Finset (Fin n)) {c, d}) :
    G.unblockedDifferential R (G.unblockedDifferential R (Finsupp.single x 1))
      ((x.swapColumns a b).swapColumns c d) = 0 := by
  rw [G.unblockedDifferential_sq_single_apply R x]
  exact G.sum_unblockedCoefficient_mul_unblockedCoefficient_eq_zero_of_disjoint R x hab hcd
    hdisjoint

end GridDiagram

end TauCeti
