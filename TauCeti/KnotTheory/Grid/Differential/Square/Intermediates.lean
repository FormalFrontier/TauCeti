/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Backtracking

/-!
# Intermediate states in two column swaps

The support of the square of the fully blocked grid differential is contained in the states
reached from `x` by two nontrivial column swaps. This file records the exact finite set of possible
intermediate states between a source `x` and a target `z`: the intersection of their one-swap
neighbour sets.

For a diagonal path `x → y → x`, this set is exactly the full one-swap neighbour set of
`x`. For a nondiagonal path, conjugating the first transposition by the second gives another
factorization through a distinct intermediate state. Consequently every nonempty nondiagonal
intermediate set has at least two elements.

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
* `TauCeti.GridState.twoStepColumnSwapIntermediates_self`: the intermediates between `x` and
  itself are exactly its one-swap neighbours.
* `TauCeti.GridState.one_lt_card_twoStepColumnSwapIntermediates`: a nondiagonal two-step
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

/-- A state is an intermediate between `x` and `z` exactly when it is reached from `x` by one
nontrivial column swap and `z` is reached from it by another. -/
theorem mem_twoStepColumnSwapIntermediates_iff_mem_columnSwapNeighbors {x y z : GridState n} :
    y ∈ x.twoStepColumnSwapIntermediates z ↔
      y ∈ x.columnSwapNeighbors ∧ z ∈ y.columnSwapNeighbors := by
  rw [mem_twoStepColumnSwapIntermediates]
  constructor
  · exact fun h => ⟨h.1, mem_columnSwapNeighbors_comm.mp h.2⟩
  · exact fun h => ⟨h.1, mem_columnSwapNeighbors_comm.mpr h.2⟩

/-- An expanded membership form for the intermediate states in a two-swap path. -/
theorem mem_twoStepColumnSwapIntermediates_iff_exists_swaps {x y z : GridState n} :
    y ∈ x.twoStepColumnSwapIntermediates z ↔
      ∃ a b c d : Fin n,
        a ≠ b ∧ c ≠ d ∧ y = x.swapColumns a b ∧ z = y.swapColumns c d := by
  rw [mem_twoStepColumnSwapIntermediates_iff_mem_columnSwapNeighbors]
  simp only [mem_columnSwapNeighbors]
  constructor
  · rintro ⟨⟨a, b, hab, hy⟩, c, d, hcd, hz⟩
    exact ⟨a, b, c, d, hab, hcd, hy, hz⟩
  · rintro ⟨a, b, c, d, hab, hcd, hy, hz⟩
    exact ⟨⟨a, b, hab, hy⟩, c, d, hcd, hz⟩

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

/-- Applying the second of two distinct nontrivial column swaps first produces a distinct
intermediate state.

The remaining swap is the conjugate of the first one. -/
theorem swapColumns_mem_twoStepColumnSwapIntermediates_ne
    (x : GridState n) {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (hpairs : s(a, b) ≠ s(c, d)) :
    x.swapColumns c d ∈
        x.twoStepColumnSwapIntermediates ((x.swapColumns a b).swapColumns c d) ∧
      x.swapColumns c d ≠ x.swapColumns a b := by
  constructor
  · rw [mem_twoStepColumnSwapIntermediates_iff_mem_columnSwapNeighbors]
    refine ⟨mem_columnSwapNeighbors.mpr ⟨c, d, hcd, rfl⟩, ?_⟩
    rw [mem_columnSwapNeighbors]
    refine ⟨Equiv.swap c d a, Equiv.swap c d b, (Equiv.swap c d).injective.ne hab, ?_⟩
    exact x.swapColumns_swapColumns_conj a b c d
  · intro h
    exact hpairs (sym2_mk_eq_of_swapColumns_eq (x := x) hcd hab h).symm

/-- Every intermediate state on a nondiagonal two-step path has a distinct alternative
intermediate state. -/
theorem exists_mem_twoStepColumnSwapIntermediates_ne_of_mem_of_ne
    {x y z : GridState n} (hy : y ∈ x.twoStepColumnSwapIntermediates z) (hzx : z ≠ x) :
    ∃ y' ∈ x.twoStepColumnSwapIntermediates z, y' ≠ y := by
  rw [mem_twoStepColumnSwapIntermediates_iff_exists_swaps] at hy
  obtain ⟨a, b, c, d, hab, hcd, rfl, rfl⟩ := hy
  have hpairs : s(a, b) ≠ s(c, d) := by
    intro hpairs
    exact hzx ((swapColumns_swapColumns_eq_self_iff_sym2_mk_eq x hab hcd).mpr hpairs)
  exact ⟨x.swapColumns c d,
    x.swapColumns_mem_twoStepColumnSwapIntermediates_ne hab hcd hpairs⟩

/-- A nondiagonal two-step neighbour has at least two possible intermediate states. -/
theorem one_lt_card_twoStepColumnSwapIntermediates {x z : GridState n}
    (hz : z ∈ x.twoStepColumnSwapNeighbors) (hzx : z ≠ x) :
    1 < (x.twoStepColumnSwapIntermediates z).card := by
  obtain ⟨y, hy⟩ := nonempty_twoStepColumnSwapIntermediates_iff.mpr hz
  obtain ⟨y', hy', hy'ne⟩ :=
    exists_mem_twoStepColumnSwapIntermediates_ne_of_mem_of_ne hy hzx
  exact Finset.one_lt_card.mpr ⟨y, hy, y', hy', hy'ne.symm⟩

end GridState

end TauCeti
