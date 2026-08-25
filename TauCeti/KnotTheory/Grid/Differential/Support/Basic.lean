/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Complex

/-!
# Support of the fully blocked grid differential

A grid rectangle from `x` to `y` exists only when the two states differ at exactly two columns,
where they exchange their rows: `RectangleSwap.lean` records that the target of any oriented
rectangle is `y = x.swapColumns R.left R.right` for the two distinct side columns. Reading this
backwards bounds the *support* of the fully blocked grid differential: the coefficient of `y` in
`∂ x` can only be nonzero when `y` is one of the finitely many column transpositions of `x`.

This is the structural fact that makes the fully blocked complex computable. Although there are
`n!` grid states, the differential of a generator only ever reaches the `O(n²)` states obtained
by swapping a pair of columns, so an evaluation of `∂` never has to range over all of `GridState
n`. It is also a step the rectangle-pairing `∂² = 0` argument relies on: a length-two sequence of
rectangles `x → y → z` passes through a column transposition `y` of `x`, not an arbitrary state.

## Key API

* `TauCeti.GridState.columnSwapNeighbors`: the grid states obtained from `x` by transposing a
  pair of distinct columns -- the states a rectangle from `x` can reach.

## Main results

* `TauCeti.GridDiagram.exists_swapColumns_of_fullyBlockedRectangleCount_ne_zero`: a nonzero
  differential coefficient forces the target to be a column transposition of the source.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount_eq_zero_of_forall_ne`: the coefficient vanishes
  whenever the target is not any column transposition of the source.
* `TauCeti.GridDiagram.fullyBlockedDifferentialOnGenerator_support_subset` and
  `TauCeti.GridDiagram.fullyBlockedDifferential_single_support_subset`: the differential of a
  generator is supported on the column-swap neighbours of the state.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3,
"The complexes and `∂² = 0`", and the "grid homology computes" acceptance criterion. The
column-transposition picture of a rectangle move follows Ozsváth--Stipsicz--Szabó, *Grid Homology
for Knots and Links*, Chapters 3 and 4.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) {x y : GridState n}

/-- A nonzero fully blocked rectangle count produces an oriented rectangle, hence at least one
fully blocked rectangle exists between the two states. -/
theorem fullyBlockedRectangles_nonempty_of_count_ne_zero
    (h : G.fullyBlockedRectangleCount x y ≠ 0) : (G.fullyBlockedRectangles x y).Nonempty := by
  refine Finset.nonempty_of_ne_empty fun he => h ?_
  rw [fullyBlockedRectangleCount_def, he, Finset.card_empty, Nat.cast_zero]

/-- The fully blocked rectangle count vanishes whenever the target is not any column transposition
of the source. This is the contrapositive of
`exists_swapColumns_of_fullyBlockedRectangleCount_ne_zero`. -/
theorem fullyBlockedRectangleCount_eq_zero_of_forall_ne
    (h : ∀ c d : Fin n, c ≠ d → y ≠ x.swapColumns c d) :
    G.fullyBlockedRectangleCount x y = 0 := by
  by_contra hne
  obtain ⟨c, d, hcd, hy⟩ := G.exists_swapColumns_of_fullyBlockedRectangleCount_ne_zero x y hne
  exact h c d hcd hy

/-- The fully blocked rectangle count is supported on column transpositions: if `y` is not a
column-swap neighbour of `x`, the coefficient is zero. -/
theorem fullyBlockedRectangleCount_eq_zero_of_notMem_columnSwapNeighbors
    (h : y ∉ x.columnSwapNeighbors) : G.fullyBlockedRectangleCount x y = 0 :=
  G.fullyBlockedRectangleCount_eq_zero_of_forall_ne fun c d hcd hy =>
    h (GridState.mem_columnSwapNeighbors.mpr ⟨c, d, hcd, hy⟩)

/-- The coefficient of the fully blocked differential on a generator vanishes off the column-swap
neighbours of the state. -/
theorem fullyBlockedDifferentialOnGenerator_apply_eq_zero_of_notMem_columnSwapNeighbors
    (x : GridState n) {y : GridState n} (h : y ∉ x.columnSwapNeighbors) :
    G.fullyBlockedDifferentialOnGenerator x y = 0 := by
  rw [fullyBlockedDifferentialOnGenerator_apply]
  exact G.fullyBlockedRectangleCount_eq_zero_of_notMem_columnSwapNeighbors h

/-- The fully blocked differential of a generator `x` is supported on the column-swap neighbours
of `x`: although there are `n!` grid states, `∂ x` only reaches the states obtained by
transposing a pair of columns. -/
theorem fullyBlockedDifferentialOnGenerator_support_subset (x : GridState n) :
    (G.fullyBlockedDifferentialOnGenerator x).support ⊆ x.columnSwapNeighbors := by
  intro y hy
  by_contra hmem
  exact (Finsupp.mem_support_iff.mp hy)
    (G.fullyBlockedDifferentialOnGenerator_apply_eq_zero_of_notMem_columnSwapNeighbors x hmem)

/-- The number of states reached by the fully blocked differential of a generator is at most the
number of column-swap neighbours of the state. -/
theorem fullyBlockedDifferentialOnGenerator_support_card_le (x : GridState n) :
    (G.fullyBlockedDifferentialOnGenerator x).support.card ≤ x.columnSwapNeighbors.card :=
  Finset.card_le_card (G.fullyBlockedDifferentialOnGenerator_support_subset x)

/-- The fully blocked differential of a single generator, taken through the linear map, is
supported on the column-swap neighbours of the state. -/
theorem fullyBlockedDifferential_single_support_subset (x : GridState n) :
    (G.fullyBlockedDifferential (Finsupp.single x 1)).support ⊆ x.columnSwapNeighbors := by
  rw [fullyBlockedDifferential_single]
  exact G.fullyBlockedDifferentialOnGenerator_support_subset x

end GridDiagram

end TauCeti
