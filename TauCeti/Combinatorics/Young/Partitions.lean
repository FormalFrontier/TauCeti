/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.Combinatorics.Young.Diagram

/-!
# Partitions and Young diagrams

This file relates partitions of `n` and Young diagrams with `n` cells by a pair of direct
constructions: `TauCeti.diagramOf` builds the Young diagram whose rows are the decreasingly
sorted parts of a partition, and `TauCeti.toPartition` reads the row lengths of a sized diagram
back as a partition. The two constructions are inverse to each other, which packages as the
equivalence `TauCeti.partitionEquivYoungDiagram`.

## References

* [Mathlib PR #39722](https://github.com/leanprover-community/mathlib4/pull/39722)
  (Kevin Gomez) — the open Mathlib PR linking `Nat.Partition` to `YoungDiagram`, whose
  direct `ofPartition`/`toPartition` design this file adopts, in place of composing
  equivalences.
-/

public section

namespace TauCeti

/-- The Young diagram of a partition: its rows are the decreasingly sorted parts. -/
def diagramOf {n : ℕ} (μ : n.Partition) : YoungDiagram :=
  YoungDiagram.ofRowLens (μ.parts.sort (· ≥ ·))
    (Multiset.pairwise_sort μ.parts (· ≥ ·)).sortedGE

/-- The row lengths of a partition's Young diagram are its decreasingly sorted parts. -/
@[simp]
theorem rowLens_diagramOf {n : ℕ} (μ : n.Partition) :
    (diagramOf μ).rowLens = μ.parts.sort (· ≥ ·) :=
  YoungDiagram.rowLens_ofRowLens_eq_self fun _ hx =>
    μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hx)

/-- The Young diagram of a partition has the size of the partition. -/
@[simp]
theorem card_diagramOf {n : ℕ} (μ : n.Partition) : (diagramOf μ).card = n := by
  rw [← YoungDiagram.sum_rowLens, rowLens_diagramOf, ← Multiset.sum_coe, Multiset.sort_eq]
  exact μ.parts_sum

/-- The row lengths of the Young diagram of a partition are its decreasingly sorted parts, padded
by zeros. -/
@[simp]
theorem rowLen_diagramOf {n : ℕ} (ν : n.Partition) (i : ℕ) :
    (diagramOf ν).rowLen i = (ν.parts.sort (· ≥ ·)).getD i 0 := by
  rw [← YoungDiagram.getD_rowLens, rowLens_diagramOf]

/-- **The Young diagram of the partition `(1ⁿ)` is a single column**: every part is `1`, so every
row has at most one cell. -/
theorem rowLen_diagramOf_ones_le_one (n i : ℕ) :
    (diagramOf (Nat.Partition.ones n)).rowLen i ≤ 1 := by
  rw [rowLen_diagramOf, Nat.Partition.ones_parts]
  rcases lt_or_ge i ((Multiset.replicate n 1).sort (· ≥ ·)).length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact le_of_eq (Multiset.eq_of_mem_replicate
      ((Multiset.mem_sort (· ≥ ·)).mp (List.getElem_mem hi)))
  · rw [List.getD_eq_default _ _ hi]
    exact Nat.zero_le 1

/-- **The Young diagram of the partition `(n)` has at most one row**: for `n > 0` its only part is
`n`, so there is nothing below the first row, and for `n = 0` the diagram is empty. -/
theorem colLen_diagramOf_indiscrete_le_one (n : ℕ) :
    (diagramOf (Nat.Partition.indiscrete n)).colLen 0 ≤ 1 := by
  have hlen : ((Nat.Partition.indiscrete n).parts.sort (· ≥ ·)).length ≤ 1 := by
    rw [Multiset.length_sort]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [Nat.Partition.indiscrete_parts hn]
      simp
  have hrow : (diagramOf (Nat.Partition.indiscrete n)).rowLen 1 = 0 := by
    rw [rowLen_diagramOf, List.getD_eq_default _ _ hlen]
  refine Nat.le_of_not_lt fun hlt => ?_
  have hmem : ((1 : ℕ), (0 : ℕ)) ∈ diagramOf (Nat.Partition.indiscrete n) :=
    YoungDiagram.mem_iff_lt_colLen.mpr hlt
  exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp hmem) (by omega)

/-- The partition of the cells of a Young diagram: its parts are the row lengths. -/
def toPartition {n : ℕ} (μ : YoungDiagram) (h : μ.card = n) : n.Partition where
  parts := μ.rowLens
  parts_pos := fun {x} hx => μ.pos_of_mem_rowLens x (Multiset.mem_coe.mp hx)
  parts_sum := by rw [Multiset.sum_coe, YoungDiagram.sum_rowLens, h]

/-- The parts of the partition of a sized Young diagram are its row lengths. -/
@[simp]
theorem toPartition_parts {n : ℕ} (μ : YoungDiagram) (h : μ.card = n) :
    (toPartition μ h).parts = μ.rowLens := by
  rfl

/-- Reading back the row lengths of the Young diagram of a partition recovers the partition. -/
@[simp]
theorem toPartition_diagramOf {n : ℕ} (μ : n.Partition) :
    toPartition (diagramOf μ) (card_diagramOf μ) = μ := by
  apply Nat.Partition.ext
  rw [toPartition_parts, rowLens_diagramOf, Multiset.sort_eq]

/-- The Young diagram whose rows are the row lengths of a sized Young diagram is that
diagram. -/
@[simp]
theorem diagramOf_toPartition {n : ℕ} (μ : YoungDiagram) (h : μ.card = n) :
    diagramOf (toPartition μ h) = μ := by
  simp only [diagramOf, toPartition_parts, YoungDiagram.sort_coe_rowLens]
  exact YoungDiagram.ofRowLens_to_rowLens_eq_self

/-- Partitions of `n` are equivalent to Young diagrams with `n` cells. -/
def partitionEquivYoungDiagram (n : ℕ) :
    n.Partition ≃ {μ : YoungDiagram // μ.card = n} where
  toFun μ := ⟨diagramOf μ, card_diagramOf μ⟩
  invFun μ := toPartition μ.1 μ.2
  left_inv μ := toPartition_diagramOf μ
  right_inv μ := Subtype.ext (diagramOf_toPartition μ.1 μ.2)

/-- The Young diagram associated to a partition by the equivalence is `TauCeti.diagramOf`. -/
@[simp]
theorem partitionEquivYoungDiagram_apply (n : ℕ) (μ : n.Partition) :
    partitionEquivYoungDiagram n μ = ⟨diagramOf μ, card_diagramOf μ⟩ := by
  rfl

/-- The partition associated to a sized Young diagram by the equivalence is
`TauCeti.toPartition`. -/
@[simp]
theorem partitionEquivYoungDiagram_symm_apply (n : ℕ) (μ : {μ : YoungDiagram // μ.card = n}) :
    (partitionEquivYoungDiagram n).symm μ = toPartition μ.1 μ.2 := by
  rfl

/-- The Young diagram construction is injective on partitions of a fixed size. -/
theorem diagramOf_injective {n : ℕ} : Function.Injective (diagramOf (n := n)) :=
  fun μ ν h => (partitionEquivYoungDiagram n).injective <| by
    simp only [partitionEquivYoungDiagram_apply, Subtype.mk.injEq]
    exact h

/-- The **shape partition** of a Young diagram: the partition of `μ.card` whose parts are the row
lengths. -/
def shapePartition (μ : YoungDiagram) : μ.card.Partition :=
  toPartition μ rfl

/-- The Young diagram of the shape partition of a Young diagram is that diagram. -/
@[simp]
theorem diagramOf_shapePartition (μ : YoungDiagram) : diagramOf (shapePartition μ) = μ :=
  diagramOf_toPartition μ rfl

/-- The parts of the shape partition are the row lengths of the diagram. -/
@[simp]
theorem shapePartition_parts (μ : YoungDiagram) :
    (shapePartition μ).parts = μ.rowLens := by
  rfl

/-- Sorting the parts of the shape partition into decreasing order returns the row lengths, which
are already decreasing.  This is not a `simp` lemma: `simp` reaches the same normal form through
`shapePartition_parts` and `TauCeti.YoungDiagram.sort_coe_rowLens`. -/
theorem shapePartition_parts_sort (μ : YoungDiagram) :
    (shapePartition μ).parts.sort (· ≥ ·) = μ.rowLens := by
  rw [shapePartition_parts, YoungDiagram.sort_coe_rowLens]

end TauCeti
