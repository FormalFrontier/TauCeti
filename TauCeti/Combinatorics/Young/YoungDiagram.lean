/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# The row lengths of a Young diagram add up to its size

Mathlib's `YoungDiagram.rowLens` records the lengths of the rows of a Young diagram.  This file
proves that these lengths sum to the number of cells of the diagram.
-/

public section

namespace TauCeti

namespace YoungDiagram

/-- Transposing a Young diagram preserves its number of cells. -/
@[simp]
theorem card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  change ((Equiv.prodComm ℕ ℕ).finsetCongr μ.cells).card = μ.cells.card
  rw [Equiv.finsetCongr_apply, Finset.card_map]

/-- The sum of the row lengths of a Young diagram is its number of cells. -/
@[simp]
theorem sum_rowLens (μ : YoungDiagram) : μ.rowLens.sum = μ.card := by
  have sum_list_range (f : ℕ → ℕ) :
      ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp
  have hrange : μ.rowLens.sum = ∑ i ∈ Finset.range (μ.colLen 0), μ.rowLen i := by
    rw [_root_.YoungDiagram.rowLens, sum_list_range]
  rw [hrange]
  symm
  calc
    μ.card =
        ∑ i ∈ Finset.range (μ.colLen 0),
          (μ.cells.filter fun c => c.fst = i).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simpa using
        (_root_.YoungDiagram.mem_iff_lt_colLen.mp hc).trans_le
          (μ.colLen_anti 0 c.snd c.snd.zero_le)
    _ = ∑ i ∈ Finset.range (μ.colLen 0), μ.rowLen i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (μ.rowLen_eq_card (i := i)).symm

end YoungDiagram

end TauCeti
