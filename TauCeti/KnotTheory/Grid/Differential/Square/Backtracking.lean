/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Support
public import Mathlib.Data.Sym.Sym2

/-!
# Backtracking in the two-step grid differential support

The support of the square of the fully blocked grid differential is already bounded by
`GridState.twoStepColumnSwapNeighbors`: states reached from `x` by two nontrivial column
transpositions. This file records the first exact feature of that two-step support. A path that
swaps the same pair of columns twice returns to the starting state, so the source state appears in
its own two-step neighbour set exactly when the grid has at least two columns.

This is small but useful bookkeeping for the later `∂² = 0` rectangle-pairing argument: diagonal
targets lie in the two-step search space exactly through such backtracking when `2 ≤ n`. Grids of
size `0` and `1` have no two-step targets at all, so any coefficient-level vanishing there follows
from the existing small-grid differential support API rather than from a cancellation argument in
this file.

## Main results

* `TauCeti.GridState.self_mem_twoStepColumnSwapNeighbors_of_ne`: swapping a pair of distinct
  columns and then swapping it back puts `x` in its own two-step neighbour set.
* `TauCeti.GridState.sym2_mk_eq_of_swapColumns_swapColumns_eq_self`: any diagonal two-step
  witness swaps the same unordered pair of columns twice.
* `TauCeti.GridState.self_mem_twoStepColumnSwapNeighbors_iff_exists_pair_ne`: this is possible
  exactly when there is a distinct pair of columns.
* `TauCeti.GridState.self_mem_twoStepColumnSwapNeighbors_iff_two_le`: equivalently, exactly when
  `2 ≤ n`.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3,
"The complexes and `∂² = 0`", where the square-zero proof pairs two-step rectangle
decompositions. The column-transposition model of rectangle targets follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3 and 4.
-/

public section

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- Swapping a distinct pair of columns and then swapping the same pair back puts the source state
in its own two-step column-swap neighbour set. -/
theorem self_mem_twoStepColumnSwapNeighbors_of_ne (x : GridState n) {a b : Fin n}
    (hab : a ≠ b) : x ∈ x.twoStepColumnSwapNeighbors := by
  rw [mem_twoStepColumnSwapNeighbors]
  refine ⟨x.swapColumns a b, GridState.mem_columnSwapNeighbors.mpr ⟨a, b, hab, rfl⟩, ?_⟩
  rw [mem_columnSwapNeighbors]
  exact ⟨a, b, hab, by simp⟩

/-- A diagonal two-step column-swap witness must swap the same unordered pair of columns twice. -/
theorem sym2_mk_eq_of_swapColumns_swapColumns_eq_self (x : GridState n) {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (h : (x.swapColumns a b).swapColumns c d = x) :
    s(a, b) = s(c, d) := by
  have hswap : x.swapColumns a b = x.swapColumns c d := by
    simpa using congrArg (fun y : GridState n => y.swapColumns c d) h
  exact sym2_mk_eq_of_swapColumns_eq hab hcd hswap

/-- Two nontrivial column swaps form a diagonal two-step witness exactly when they use the same
unordered pair of columns. -/
theorem swapColumns_swapColumns_eq_self_iff_sym2_mk_eq (x : GridState n) {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) : (x.swapColumns a b).swapColumns c d = x ↔ s(a, b) = s(c, d) := by
  constructor
  · exact x.sym2_mk_eq_of_swapColumns_swapColumns_eq_self hab hcd
  · intro hsym
    rw [Sym2.eq, Sym2.rel_iff'] at hsym
    rcases hsym with hpair | hpair
    · cases hpair
      exact GridState.swapColumns_swapColumns a b x
    · cases hpair
      simp [GridState.swapColumns_comm]

/-- The source state appears in its own two-step neighbour set exactly when there is a distinct
pair of grid columns. -/
theorem self_mem_twoStepColumnSwapNeighbors_iff_exists_pair_ne (x : GridState n) :
    x ∈ x.twoStepColumnSwapNeighbors ↔ ∃ a b : Fin n, a ≠ b := by
  constructor
  · intro hx
    rw [mem_twoStepColumnSwapNeighbors] at hx
    obtain ⟨y, hy, _hyx⟩ := hx
    rw [mem_columnSwapNeighbors] at hy
    exact hy.imp fun a ha => ha.imp fun b hb => hb.1
  · rintro ⟨a, b, hab⟩
    exact x.self_mem_twoStepColumnSwapNeighbors_of_ne hab

/-- If the grid has at least two columns, the source state is a two-step neighbour of itself. -/
theorem self_mem_twoStepColumnSwapNeighbors_of_two_le (x : GridState n) (hn : 2 ≤ n) :
    x ∈ x.twoStepColumnSwapNeighbors := by
  rw [self_mem_twoStepColumnSwapNeighbors_iff_exists_pair_ne]
  refine ⟨⟨0, Nat.lt_of_lt_of_le (by decide) hn⟩,
    ⟨1, Nat.lt_of_lt_of_le (by decide) hn⟩, ?_⟩
  intro h
  exact Nat.zero_ne_one (congrArg Fin.val h)

/-- The source state is a two-step neighbour of itself exactly in grid size at least two. -/
@[simp 1100]
theorem self_mem_twoStepColumnSwapNeighbors_iff_two_le (x : GridState n) :
    x ∈ x.twoStepColumnSwapNeighbors ↔ 2 ≤ n := by
  constructor
  · intro hx
    rw [self_mem_twoStepColumnSwapNeighbors_iff_exists_pair_ne] at hx
    obtain ⟨a, b, hab⟩ := hx
    have hcard : 1 < Fintype.card (Fin n) :=
      Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
    exact Nat.succ_le_of_lt (by simpa [Fintype.card_fin] using hcard)
  · intro hn
    exact x.self_mem_twoStepColumnSwapNeighbors_of_two_le hn

end GridState

end TauCeti
