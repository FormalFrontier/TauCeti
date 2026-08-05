/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.Combinatorics.Young.Diagram

/-!
# Partitions and Young diagrams

This file gives the equivalence between partitions of `n` and Young diagrams with `n` cells.  It
sorts the multiset of parts into decreasing row lengths, using
`TauCeti.Nat.Partition.equivSortedParts` and `TauCeti.YoungDiagram.sum_rowLens`.
-/

public section

namespace TauCeti

/-- Partitions of `n` are equivalent to Young diagrams with `n` cells. -/
noncomputable def partitionEquivYoungDiagram (n : ℕ) :
    n.Partition ≃ {μ : YoungDiagram // μ.card = n} :=
  (Nat.Partition.equivSortedParts n).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter
      (fun w : List ℕ => w.SortedGE ∧ ∀ x ∈ w, 0 < x)
        (fun w => w.sum = n)).symm.trans
      (YoungDiagram.equivListRowLens.symm.subtypeEquiv
        (q := fun μ => μ.card = n) fun w => by
          rw [← YoungDiagram.sum_rowLens, _root_.YoungDiagram.equivListRowLens_symm_apply,
            _root_.YoungDiagram.rowLens_ofRowLens_eq_self w.2.2]))

/-- The Young diagram associated to a partition is the one built from its decreasing parts by
`YoungDiagram.ofRowLens`. -/
theorem partitionEquivYoungDiagram_apply_coe (n : ℕ) (p : n.Partition) :
    (partitionEquivYoungDiagram n p).1 =
      _root_.YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·))
        (Multiset.pairwise_sort p.parts (· ≥ ·)).sortedGE := by
  simp only [partitionEquivYoungDiagram, Equiv.trans_apply, Equiv.subtypeEquiv_apply,
    _root_.YoungDiagram.equivListRowLens_symm_apply]
  have hinter :
      ↑↑((Equiv.subtypeSubtypeEquivSubtypeInter
          (fun w : List ℕ => w.SortedGE ∧ ∀ x ∈ w, 0 < x)
          (fun w => w.sum = n)).symm (Nat.Partition.equivSortedParts n p)) =
        (Nat.Partition.equivSortedParts n p).1 := by
    symm
    simpa only [Equiv.apply_symm_apply] using
      (Equiv.subtypeSubtypeEquivSubtypeInter_apply_coe
        (fun w : List ℕ => w.SortedGE ∧ ∀ x ∈ w, 0 < x)
        (fun w => w.sum = n)
        ((Equiv.subtypeSubtypeEquivSubtypeInter
          (fun w : List ℕ => w.SortedGE ∧ ∀ x ∈ w, 0 < x)
          (fun w => w.sum = n)).symm (Nat.Partition.equivSortedParts n p)))
  have hlists := hinter.trans (Nat.Partition.equivSortedParts_apply_coe n p)
  apply _root_.YoungDiagram.ext
  ext c
  rw [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_cells,
    _root_.YoungDiagram.mem_ofRowLens, _root_.YoungDiagram.mem_ofRowLens]
  rw [hlists]

/-- The Young diagram associated to a partition has its decreasing parts as row lengths. -/
@[simp]
theorem partitionEquivYoungDiagram_apply_rowLens (n : ℕ) (p : n.Partition) :
    (partitionEquivYoungDiagram n p).1.rowLens = p.parts.sort (· ≥ ·) := by
  rw [partitionEquivYoungDiagram_apply_coe n p]
  exact _root_.YoungDiagram.rowLens_ofRowLens_eq_self fun x hx =>
    p.parts_pos ((Multiset.mem_sort (r := (· ≥ ·))).mp hx)

/-- Reading the row lengths of a sized Young diagram recovers the partition's parts. -/
@[simp]
theorem partitionEquivYoungDiagram_symm_apply_parts (n : ℕ) (μ : {μ : YoungDiagram // μ.card = n}) :
    ((partitionEquivYoungDiagram n).symm μ).parts = μ.1.rowLens := by
  have h := partitionEquivYoungDiagram_apply_rowLens n
    ((partitionEquivYoungDiagram n).symm μ)
  rw [Equiv.apply_symm_apply] at h
  calc
    ((partitionEquivYoungDiagram n).symm μ).parts =
        ↑(((partitionEquivYoungDiagram n).symm μ).parts.sort (· ≥ ·)) :=
      (Multiset.sort_eq _ _).symm
    _ = ↑μ.1.rowLens := congrArg (fun w : List ℕ => (↑w : Multiset ℕ)) h.symm

end TauCeti
