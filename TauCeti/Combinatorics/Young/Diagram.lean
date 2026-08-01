/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.List.GetD

/-!
# Counting the cells of a Young diagram by rows

Mathlib's `YoungDiagram.rowLens` records the lengths of the rows of a Young diagram.  This file
counts the cells of a diagram row by row: the row lengths sum to the number of cells, and the
first `k` row lengths sum to the number of cells lying in the first `k` rows, whether those
lengths are summed as `∑ i ∈ Finset.range k, μ.rowLen i` or as `(μ.rowLens.take k).sum`.

The partial sums are the shape of every dominance statement about partitions, since dominance
compares partial sums of decreasingly sorted parts, and the sorted parts of a partition are the
row lengths of its Young diagram.
-/

public section

namespace TauCeti

namespace YoungDiagram

/-- Transposing a Young diagram preserves its number of cells. -/
@[simp]
theorem card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  apply Finset.card_equiv (Equiv.prodComm ℕ ℕ)
  intro c
  simp

private theorem sum_list_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A row past the last one of a Young diagram is empty. -/
theorem rowLen_eq_zero_of_colLen_le {μ : YoungDiagram} {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  exact absurd (_root_.YoungDiagram.mem_iff_lt_colLen.mp
    (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h))) (Nat.not_lt.mpr hi)

/-- Reading the length of a row off `YoungDiagram.rowLens`, with `0` for the rows past the last
one. -/
theorem getD_rowLens (μ : YoungDiagram) (i : ℕ) : μ.rowLens.getD i 0 = μ.rowLen i := by
  by_cases hi : i < μ.rowLens.length
  · rw [List.getD_eq_getElem _ _ hi, _root_.YoungDiagram.get_rowLens]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
      rowLen_eq_zero_of_colLen_le
        (le_of_eq_of_le _root_.YoungDiagram.length_rowLens.symm (Nat.le_of_not_lt hi))]

/-- The first `k` row lengths of a Young diagram count its cells in the first `k` rows. -/
theorem sum_range_rowLen_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    ∑ i ∈ Finset.range k, μ.rowLen i = (μ.cells.filter fun c => c.1 < k).card := by
  symm
  calc
    (μ.cells.filter fun c => c.1 < k).card =
        ∑ i ∈ Finset.range k,
          ((μ.cells.filter fun c => c.1 < k).filter fun c => c.1 = i).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter] at hc
      exact Finset.mem_range.mpr hc.2
    _ = ∑ i ∈ Finset.range k, μ.rowLen i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [μ.rowLen_eq_card]
      congr 1
      ext c
      have hik : i < k := Finset.mem_range.mp hi
      simp only [Finset.mem_filter, _root_.YoungDiagram.mem_cells,
        _root_.YoungDiagram.mem_row_iff]
      aesop

/-- The first `k` entries of `YoungDiagram.rowLens` count the cells in the first `k` rows.  This
is `TauCeti.YoungDiagram.sum_range_rowLen_eq_card_filter_fst` with the truncation taken on the
list of row lengths, the form in which partial sums enter the dominance order on partitions. -/
theorem sum_take_rowLens_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    (μ.rowLens.take k).sum = (μ.cells.filter fun c => c.1 < k).card := by
  rw [_root_.YoungDiagram.rowLens, ← List.map_take, List.take_range, sum_list_range,
    ← sum_range_rowLen_eq_card_filter_fst]
  have hsub : Finset.range (min k (μ.colLen 0)) ⊆ Finset.range k := fun i hi =>
    Finset.mem_range.mpr (lt_min_iff.mp (Finset.mem_range.mp hi)).1
  refine Finset.sum_subset hsub fun i hi hi' => ?_
  exact rowLen_eq_zero_of_colLen_le
    (by simpa [lt_min_iff, Finset.mem_range.mp hi] using Finset.mem_range.not.mp hi')

/-- The sum of the row lengths of a Young diagram is its number of cells. -/
@[simp]
theorem sum_rowLens (μ : YoungDiagram) : μ.rowLens.sum = μ.card := by
  have hrange : μ.rowLens.sum = ∑ i ∈ Finset.range (μ.colLen 0), μ.rowLen i := by
    rw [_root_.YoungDiagram.rowLens, sum_list_range]
  rw [hrange, sum_range_rowLen_eq_card_filter_fst]
  refine congrArg Finset.card (Finset.filter_true_of_mem fun c hc => ?_)
  simpa using
    (_root_.YoungDiagram.mem_iff_lt_colLen.mp hc).trans_le
      (μ.colLen_anti 0 c.snd c.snd.zero_le)

end YoungDiagram

end TauCeti
