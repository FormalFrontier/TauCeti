/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Dominance
public import TauCeti.Combinatorics.Young.Partitions

/-!
# Conjugate partitions and dominance

This file defines the conjugate of a natural-number partition by transposing its Young diagram.
It proves that conjugation is an involution and reverses the dominance order.

The reversal theorem is the remaining part of the “Orders on partitions” target in Layer 0 of
the symmetric-group and Schur–Weyl roadmap.  It supplies the order duality used later for the
row/column symmetry of Specht modules and permutation modules.

## References

* W. Fulton, *Young Tableaux*, London Mathematical Society Student Texts 35, §1.1.
-/

public section

namespace TauCeti

open scoped BigOperators

private theorem sum_take_rowLens_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    (μ.rowLens.take k).sum = (μ.cells.filter fun c => c.1 < k).card := by
  rw [YoungDiagram.rowLens, ← List.map_take, List.take_range,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  symm
  calc
    (μ.cells.filter fun c => c.1 < k).card =
        ∑ i ∈ Finset.range (min k (μ.colLen 0)),
          ((μ.cells.filter fun c => c.1 < k).filter fun c => c.1 = i).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
      rw [Finset.mem_range]
      refine lt_min hc.2 ?_
      rw [← YoungDiagram.mem_iff_lt_colLen]
      exact μ.up_left_mem (by rfl) c.2.zero_le hc.1
    _ = ∑ i ∈ Finset.range (min k (μ.colLen 0)), μ.rowLen i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [μ.rowLen_eq_card]
      congr 1
      ext c
      have hik : i < k := (Finset.mem_range.mp hi).trans_le (min_le_left _ _)
      simp only [Finset.mem_filter, YoungDiagram.mem_cells, YoungDiagram.mem_row_iff]
      aesop

private theorem sum_map_min_rowLens_eq_card_filter_snd (μ : YoungDiagram) (k : ℕ) :
    (μ.rowLens.map (min k)).sum = (μ.cells.filter fun c => c.2 < k).card := by
  rw [YoungDiagram.rowLens, List.map_map,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  symm
  calc
    (μ.cells.filter fun c => c.2 < k).card =
        ∑ i ∈ Finset.range (μ.colLen 0),
          ((μ.cells.filter fun c => c.2 < k).filter fun c => c.1 = i).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
      rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen]
      exact μ.up_left_mem (by rfl) c.2.zero_le hc.1
    _ = ∑ i ∈ Finset.range (μ.colLen 0), min k (μ.rowLen i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hfiber :
          (μ.cells.filter fun c => c.2 < k).filter (fun c => c.1 = i) =
            {i} ×ˢ Finset.range (min k (μ.rowLen i)) := by
        ext c
        simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_product,
          Finset.mem_singleton, Finset.mem_range, lt_min_iff]
        rw [YoungDiagram.mem_iff_lt_rowLen]
        aesop
      rw [hfiber, Finset.card_product]
      simp

private theorem card_filter_fst_transpose (μ : YoungDiagram) (k : ℕ) :
    (μ.transpose.cells.filter fun c => c.1 < k).card =
      (μ.cells.filter fun c => c.2 < k).card := by
  change
    (((Equiv.prodComm ℕ ℕ).finsetCongr μ.cells).filter fun c => c.1 < k).card =
      (μ.cells.filter fun c => c.2 < k).card
  rw [Equiv.finsetCongr_apply]
  have hmap :
      (μ.cells.filter fun c => c.2 < k).map (Equiv.prodComm ℕ ℕ).toEmbedding =
        (μ.cells.map (Equiv.prodComm ℕ ℕ).toEmbedding).filter fun c => c.1 < k := by
    rw [Finset.map_filter]
    ext ⟨i, j⟩
    simp
  rw [← hmap, Finset.card_map]

private theorem sum_take_transpose_rowLens (μ : YoungDiagram) (k : ℕ) :
    (μ.transpose.rowLens.take k).sum = (μ.rowLens.map (min k)).sum := by
  rw [sum_take_rowLens_eq_card_filter_fst, card_filter_fst_transpose,
    sum_map_min_rowLens_eq_card_filter_snd]

private theorem sum_sub_add_mul_length_takeWhile {l : List ℕ} (hl : l.SortedGE) (k : ℕ) :
    (l.map fun x => x - k).sum +
        k * (l.takeWhile fun x => decide (k < x)).length =
      (l.takeWhile fun x => decide (k < x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hlsorted : l.SortedGE := hl.pairwise.tail.sortedGE
      by_cases ha : k < a
      · rw [List.takeWhile_cons_of_pos (by simpa using ha)]
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have htail := ih hlsorted
        rw [Nat.mul_succ]
        omega
      · have hale : a ≤ k := Nat.le_of_not_gt ha
        have htail : ∀ x ∈ l, x ≤ k := by
          intro x hx
          exact (hl.pairwise.rel_head_tail (by simpa using hx)).trans hale
        have hsum : (l.map fun x => x - k).sum = 0 := by
          apply List.sum_eq_zero
          intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          exact Nat.sub_eq_zero_of_le (htail x hx)
        rw [List.takeWhile_cons_of_neg (by simpa using ha)]
        simp only [List.map_cons, List.sum_cons, List.sum_nil, List.length_nil, mul_zero,
          add_zero, Nat.sub_eq_zero_of_le hale]
        simpa only [zero_add] using hsum

private theorem sum_take_le_mul_add_sum_sub (l : List ℕ) (k r : ℕ) :
    (l.take r).sum ≤ k * r + (l.map fun x => x - k).sum := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
      cases l with
      | nil => simp
      | cons a l =>
          simp only [List.take_succ_cons, List.sum_cons, List.map_cons, Nat.mul_succ]
          have htail := ih l
          omega

private theorem sum_min_add_sum_sub (l : List ℕ) (k : ℕ) :
    (l.map (min k)).sum + (l.map fun x => x - k).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      omega

private theorem sum_map_min_le_of_prefix_sum_le {l₁ l₂ : List ℕ}
    (hl₂ : l₂.SortedGE) (hsum : l₁.sum = l₂.sum)
    (hle : ∀ r, (l₂.take r).sum ≤ (l₁.take r).sum) (k : ℕ) :
    (l₁.map (min k)).sum ≤ (l₂.map (min k)).sum := by
  let r := (l₂.takeWhile fun x => decide (k < x)).length
  have htake :
      l₂.take r = l₂.takeWhile fun x => decide (k < x) := by
    rw [show r = (l₂.takeWhile fun x => decide (k < x)).length by rfl]
    calc
      l₂.take (l₂.takeWhile fun x => decide (k < x)).length =
          ((l₂.takeWhile fun x => decide (k < x)) ++
            l₂.dropWhile fun x => decide (k < x)).take
              (l₂.takeWhile fun x => decide (k < x)).length := by
        rw [l₂.takeWhile_append_dropWhile]
      _ = l₂.takeWhile fun x => decide (k < x) := List.take_left
  have hexcess :
      (l₂.map fun x => x - k).sum + k * r = (l₂.take r).sum := by
    rw [htake]
    exact sum_sub_add_mul_length_takeWhile hl₂ k
  have hsub :
      (l₂.map fun x => x - k).sum ≤ (l₁.map fun x => x - k).sum := by
    have hpref := hle r
    have hupper := sum_take_le_mul_add_sum_sub l₁ k r
    omega
  have hsplit₁ := sum_min_add_sum_sub l₁ k
  have hsplit₂ := sum_min_add_sum_sub l₂ k
  omega

/-- The Young diagram of a partition. -/
noncomputable def diagramOf {n : ℕ} (μ : n.Partition) : YoungDiagram :=
  (partitionEquivYoungDiagram n μ).1

/-- The Young diagram of a partition has the size of the partition. -/
@[simp]
theorem card_diagramOf {n : ℕ} (μ : n.Partition) : (diagramOf μ).card = n :=
  (partitionEquivYoungDiagram n μ).2

/-- The row lengths of a partition's Young diagram are its decreasingly sorted parts. -/
@[simp]
theorem rowLens_diagramOf {n : ℕ} (μ : n.Partition) :
    (diagramOf μ).rowLens = μ.parts.sort (· ≥ ·) :=
  partitionEquivYoungDiagram_apply_rowLens n μ

/-- The conjugate of a partition is obtained by transposing its Young diagram. -/
noncomputable def conjugate {n : ℕ} (μ : n.Partition) : n.Partition :=
  (partitionEquivYoungDiagram n).symm
    ⟨(diagramOf μ).transpose, by simp⟩

/-- The Young diagram of the conjugate partition is the transposed Young diagram. -/
@[simp]
theorem diagramOf_conjugate {n : ℕ} (μ : n.Partition) :
    diagramOf (conjugate μ) = (diagramOf μ).transpose := by
  change
    ((partitionEquivYoungDiagram n)
      ((partitionEquivYoungDiagram n).symm
        ⟨(diagramOf μ).transpose, by simp⟩)).1 =
      (diagramOf μ).transpose
  rw [Equiv.apply_symm_apply]

/-- Conjugating a partition twice recovers the original partition. -/
@[simp]
theorem conjugate_conjugate {n : ℕ} (μ : n.Partition) :
    conjugate (conjugate μ) = μ := by
  apply (partitionEquivYoungDiagram n).injective
  apply Subtype.ext
  change diagramOf (conjugate (conjugate μ)) = diagramOf μ
  rw [diagramOf_conjugate, diagramOf_conjugate, YoungDiagram.transpose_transpose]

/-- The decreasing parts of the conjugate partition are the row lengths of the transposed
diagram. -/
theorem conjugate_parts_sort {n : ℕ} (μ : n.Partition) :
    (conjugate μ).parts.sort (· ≥ ·) = (diagramOf μ).transpose.rowLens := by
  calc
    (conjugate μ).parts.sort (· ≥ ·) = (diagramOf (conjugate μ)).rowLens :=
      (rowLens_diagramOf (conjugate μ)).symm
    _ = (diagramOf μ).transpose.rowLens := congrArg YoungDiagram.rowLens (diagramOf_conjugate μ)

private theorem dominates_conjugate {n : ℕ} {μ ν : n.Partition} (h : Dominates μ ν) :
    Dominates (conjugate ν) (conjugate μ) := by
  rw [dominates_iff]
  intro k
  rw [conjugate_parts_sort, conjugate_parts_sort, sum_take_transpose_rowLens,
    sum_take_transpose_rowLens]
  rw [rowLens_diagramOf, rowLens_diagramOf]
  apply sum_map_min_le_of_prefix_sum_le
  · exact (Multiset.pairwise_sort ν.parts (· ≥ ·)).sortedGE
  · calc
      (μ.parts.sort (· ≥ ·)).sum =
          (↑(μ.parts.sort (· ≥ ·)) : Multiset ℕ).sum :=
        (Multiset.sum_coe _).symm
      _ = μ.parts.sum := congrArg Multiset.sum (Multiset.sort_eq μ.parts (· ≥ ·))
      _ = n := μ.parts_sum
      _ = ν.parts.sum := ν.parts_sum.symm
      _ = (↑(ν.parts.sort (· ≥ ·)) : Multiset ℕ).sum :=
        congrArg Multiset.sum (Multiset.sort_eq ν.parts (· ≥ ·)).symm
      _ = (ν.parts.sort (· ≥ ·)).sum := Multiset.sum_coe _
  · exact dominates_iff.mp h

/-- Conjugation of partitions reverses dominance. -/
theorem dominates_transpose_iff {n : ℕ} (μ ν : n.Partition) :
    Dominates μ ν ↔ Dominates (conjugate ν) (conjugate μ) := by
  constructor
  · exact dominates_conjugate
  · intro h
    simpa using dominates_conjugate h

end TauCeti
