/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Backtracking

/-!
# Intermediate states in two column swaps

The support of the square of the fully blocked grid differential consists of paths of two
nontrivial column swaps. This file records the exact finite set of possible intermediate states
between a source `x` and a target `z`: the intersection of their one-swap neighbour sets.

For a diagonal path `x → y → x`, this set is exactly the full one-swap neighbour set of
`x`. For a nondiagonal path, conjugating the first transposition by the second gives another
factorization through a distinct intermediate state. Consequently every nonempty nondiagonal
intermediate set has at least two elements. The conjugation argument treats both geometric cases
needed later: disjoint transpositions commute, while transpositions sharing one column satisfy
the three-column braid relation.

These state-level factorizations do not yet pair rectangles: a later juxtaposition argument must
also track which of the two rectangles with given corners is used and whether its domain avoids
the markings. They provide the finite diagonal/nondiagonal case split on which that argument is
built.

## Main definitions

* `TauCeti.GridState.twoStepColumnSwapIntermediates`: the possible middle states in a two-swap
  path from `x` to `z`.

## Main results

* `TauCeti.GridState.nonempty_twoStepColumnSwapIntermediates_iff`: the intermediate set is
  nonempty exactly for a two-step neighbour.
* `TauCeti.GridState.twoStepColumnSwapIntermediates_self`: diagonal paths are precisely the
  backtracking paths through an arbitrary one-swap neighbour.
* `TauCeti.GridState.swapColumns_swapColumns_conj`: the transposition-conjugation identity that
  reorders any two column swaps.
* `TauCeti.GridState.swapColumns_swapColumns_of_disjoint` and
  `TauCeti.GridState.swapColumns_swapColumns_overlap`: its disjoint- and shared-column forms.
* `TauCeti.GridState.one_lt_card_twoStepColumnSwapIntermediates_of_ne`: a nondiagonal two-step
  path has at least two possible intermediate states.

## References

This supplies the state-level two-step case split for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`".
The later differential proof pairs juxtaposed rectangle decompositions as in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- The grid states that can occur between `x` and `z` in a path of two nontrivial column swaps.

The definition is symmetric in the endpoints: an intermediate state is a one-swap neighbour of
both. -/
def twoStepColumnSwapIntermediates (x z : GridState n) : Finset (GridState n) :=
  x.columnSwapNeighbors ∩ z.columnSwapNeighbors

/-- A state is an intermediate between `x` and `z` exactly when it is a one-swap neighbour of
both endpoints. -/
@[simp]
theorem mem_twoStepColumnSwapIntermediates {x y z : GridState n} :
    y ∈ x.twoStepColumnSwapIntermediates z ↔
      y ∈ x.columnSwapNeighbors ∧ y ∈ z.columnSwapNeighbors := by
  simp [twoStepColumnSwapIntermediates]

/-- Swapping the two endpoints does not change their set of two-step intermediate states. -/
theorem twoStepColumnSwapIntermediates_comm (x z : GridState n) :
    x.twoStepColumnSwapIntermediates z = z.twoStepColumnSwapIntermediates x := by
  rw [twoStepColumnSwapIntermediates, twoStepColumnSwapIntermediates, Finset.inter_comm]

/-- The possible intermediate states between `x` and itself are exactly its one-swap
neighbours. -/
@[simp]
theorem twoStepColumnSwapIntermediates_self (x : GridState n) :
    x.twoStepColumnSwapIntermediates x = x.columnSwapNeighbors := by
  rw [twoStepColumnSwapIntermediates, Finset.inter_self]

/-- There is a two-step intermediate between `x` and `z` exactly when `z` is a two-step
column-swap neighbour of `x`. -/
theorem nonempty_twoStepColumnSwapIntermediates_iff {x z : GridState n} :
    (x.twoStepColumnSwapIntermediates z).Nonempty ↔ z ∈ x.twoStepColumnSwapNeighbors := by
  rw [mem_twoStepColumnSwapNeighbors]
  constructor
  · rintro ⟨y, hy⟩
    rw [mem_twoStepColumnSwapIntermediates] at hy
    exact ⟨y, hy.1, mem_columnSwapNeighbors_comm.mpr hy.2⟩
  · rintro ⟨y, hyx, hzy⟩
    exact ⟨y, mem_twoStepColumnSwapIntermediates.mpr
      ⟨hyx, mem_columnSwapNeighbors_comm.mp hzy⟩⟩

/-- Conjugating the first transposition by the second reorders two column swaps.

When the pairs are disjoint this is commutation. When they share a column, the conjugated pair is
the third pair among the three involved columns. -/
theorem swapColumns_swapColumns_conj (x : GridState n) (a b c d : Fin n) :
    (x.swapColumns a b).swapColumns c d =
      (x.swapColumns c d).swapColumns (Equiv.swap c d a) (Equiv.swap c d b) := by
  ext k
  simp only [swapColumns_apply]
  apply congrArg Fin.val
  apply x.toPerm.injective
  simpa using
    ((Equiv.swap c d).injective.swap_apply (Equiv.swap c d a) (Equiv.swap c d b)
      k)

/-- Column swaps on four distinct columns commute.

This is the disjoint-rectangle state factorization: the same endpoint is reached by applying the
two swaps in the opposite order. -/
theorem swapColumns_swapColumns_of_disjoint (x : GridState n) {a b c d : Fin n}
    (h : [a, b, c, d].Nodup) :
    (x.swapColumns a b).swapColumns c d = (x.swapColumns c d).swapColumns a b := by
  rw [x.swapColumns_swapColumns_conj a b c d]
  have hac : a ≠ c := by grind
  have had : a ≠ d := by grind
  have hbc : b ≠ c := by grind
  have hbd : b ≠ d := by grind
  rw [Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_of_ne_of_ne hbc hbd]

/-- Two swaps sharing one column can be reordered by using the third pair of columns.

For distinct `a`, `b`, and `c`, the path that swaps `a,b` and then `b,c` has the same endpoint as
the path that swaps `b,c` and then `a,c`. This is the three-column case of transposition
conjugation used for overlapping rectangles. -/
theorem swapColumns_swapColumns_overlap (x : GridState n) {a b c : Fin n}
    (h : [a, b, c].Nodup) :
    (x.swapColumns a b).swapColumns b c = (x.swapColumns b c).swapColumns a c := by
  rw [x.swapColumns_swapColumns_conj a b b c]
  have hab : a ≠ b := by grind
  have hac : a ≠ c := by grind
  rw [Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]

/-- Reordering two distinct nontrivial column swaps produces a distinct intermediate state.

The new intermediate is obtained by applying the second swap first. The remaining swap is the
conjugate of the first one. -/
theorem exists_alternate_twoStepColumnSwapIntermediate (x : GridState n) {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (hpairs : s(a, b) ≠ s(c, d)) :
    ∃ y' ∈ x.columnSwapNeighbors,
      y' ≠ x.swapColumns a b ∧
        (x.swapColumns a b).swapColumns c d ∈ y'.columnSwapNeighbors := by
  refine ⟨x.swapColumns c d, mem_columnSwapNeighbors.mpr ⟨c, d, hcd, rfl⟩, ?_, ?_⟩
  · intro h
    exact hpairs (sym2_mk_eq_of_swapColumns_eq (x := x) hcd hab h).symm
  · rw [mem_columnSwapNeighbors]
    refine ⟨Equiv.swap c d a, Equiv.swap c d b, (Equiv.swap c d).injective.ne hab, ?_⟩
    exact x.swapColumns_swapColumns_conj a b c d

/-- Every intermediate state on a nondiagonal two-step path has a distinct alternative
intermediate state. -/
theorem exists_ne_mem_twoStepColumnSwapIntermediates_of_mem_of_ne
    {x y z : GridState n} (hy : y ∈ x.twoStepColumnSwapIntermediates z) (hzx : z ≠ x) :
    ∃ y' ∈ x.twoStepColumnSwapIntermediates z, y' ≠ y := by
  rw [mem_twoStepColumnSwapIntermediates] at hy
  obtain ⟨a, b, hab, rfl⟩ := mem_columnSwapNeighbors.mp hy.1
  obtain ⟨c, d, hcd, rfl⟩ :=
    mem_columnSwapNeighbors.mp (mem_columnSwapNeighbors_comm.mpr hy.2)
  have hpairs : s(a, b) ≠ s(c, d) := by
    intro hpairs
    exact hzx ((swapColumns_swapColumns_eq_self_iff_sym2_mk_eq x hab hcd).mpr hpairs)
  obtain ⟨y', hy'x, hy'ne, hy'z⟩ :=
    x.exists_alternate_twoStepColumnSwapIntermediate hab hcd hpairs
  refine ⟨y', mem_twoStepColumnSwapIntermediates.mpr ⟨hy'x, ?_⟩, hy'ne⟩
  rw [mem_columnSwapNeighbors_comm]
  exact hy'z

/-- A nonempty nondiagonal set of two-step intermediates contains at least two states. -/
theorem one_lt_card_twoStepColumnSwapIntermediates_of_ne {x z : GridState n}
    (hne : (x.twoStepColumnSwapIntermediates z).Nonempty) (hzx : z ≠ x) :
    1 < (x.twoStepColumnSwapIntermediates z).card := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨y', hy', hy'ne⟩ :=
    exists_ne_mem_twoStepColumnSwapIntermediates_of_mem_of_ne hy hzx
  exact Finset.one_lt_card.mpr ⟨y, hy, y', hy', hy'ne.symm⟩

/-- A nondiagonal two-step neighbour has at least two possible intermediate states. -/
theorem one_lt_card_twoStepColumnSwapIntermediates {x z : GridState n}
    (hz : z ∈ x.twoStepColumnSwapNeighbors) (hzx : z ≠ x) :
    1 < (x.twoStepColumnSwapIntermediates z).card :=
  one_lt_card_twoStepColumnSwapIntermediates_of_ne
    (nonempty_twoStepColumnSwapIntermediates_iff.mpr hz) hzx

end GridState

end TauCeti
