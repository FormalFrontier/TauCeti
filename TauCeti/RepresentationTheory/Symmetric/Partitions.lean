/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
public import TauCeti.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.Combinatorics.Young.YoungDiagram

/-!
# Partitions, Young diagrams, and conjugacy classes

This file connects three indexing types used in the representation theory of the symmetric group:
partitions of `n`, Young diagrams with `n` cells, and conjugacy classes of `Equiv.Perm (Fin n)`.

The equivalence with Young diagrams sorts the multiset of parts into decreasing row lengths, using
`TauCeti.Nat.Partition.equivSortedParts` and `TauCeti.YoungDiagram.sum_rowLens`.  The equivalence
with conjugacy classes uses Mathlib's partition of a permutation, including the fixed points as
parts of size one.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 0.
-/

public section

namespace TauCeti

open Equiv

/-- Partitions of `n` are equivalent to Young diagrams with `n` cells. -/
@[expose] noncomputable def partitionEquivYoungDiagram (n : ℕ) :
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
theorem partitionEquivYoungDiagram_apply_coe (n : ℕ) (p : n.Partition)
    (hw : (p.parts.sort (· ≥ ·)).SortedGE) :
    (partitionEquivYoungDiagram n p).1 =
      _root_.YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) hw :=
  rfl

/-- The Young diagram associated to a partition has its decreasing parts as row lengths. -/
@[simp]
theorem partitionEquivYoungDiagram_apply_rowLens (n : ℕ) (p : n.Partition) :
    (partitionEquivYoungDiagram n p).1.rowLens = p.parts.sort (· ≥ ·) := by
  rw [partitionEquivYoungDiagram_apply_coe n p
    (Multiset.pairwise_sort p.parts (· ≥ ·)).sortedGE]
  exact _root_.YoungDiagram.rowLens_ofRowLens_eq_self fun x hx =>
    p.parts_pos ((Multiset.mem_sort (r := (· ≥ ·))).mp hx)

/-- Reading the row lengths of a sized Young diagram recovers the partition's parts. -/
@[simp]
theorem partitionEquivYoungDiagram_symm_apply_parts (n : ℕ)
    (μ : {μ : YoungDiagram // μ.card = n}) :
    ((partitionEquivYoungDiagram n).symm μ).parts = μ.1.rowLens := by
  have h := partitionEquivYoungDiagram_apply_rowLens n
    ((partitionEquivYoungDiagram n).symm μ)
  rw [Equiv.apply_symm_apply] at h
  calc
    ((partitionEquivYoungDiagram n).symm μ).parts =
        ↑(((partitionEquivYoungDiagram n).symm μ).parts.sort (· ≥ ·)) :=
      (Multiset.sort_eq _ _).symm
    _ = ↑μ.1.rowLens := congrArg (fun w : List ℕ => (↑w : Multiset ℕ)) h.symm

/-- The partition of `n` obtained from a permutation of `Fin n`. -/
@[expose] def finPermPartition (n : ℕ) (σ : Equiv.Perm (Fin n)) : n.Partition where
  parts := σ.partition.parts
  parts_pos := σ.partition.parts_pos
  parts_sum := by simpa using σ.partition.parts_sum

/-- The parts of `finPermPartition n σ` are the parts of Mathlib's partition of `σ`. -/
@[simp]
theorem finPermPartition_parts (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (finPermPartition n σ).parts = σ.partition.parts :=
  rfl

/-- Two permutations of `Fin n` have the same sized partition exactly when their Mathlib
partitions agree. -/
@[simp]
theorem finPermPartition_eq_iff (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    finPermPartition n σ = finPermPartition n τ ↔ σ.partition = τ.partition := by
  constructor <;> intro h <;> apply Nat.Partition.ext
  · simpa only [finPermPartition_parts] using congrArg Nat.Partition.parts h
  · simpa only [finPermPartition_parts] using congrArg Nat.Partition.parts h

/-- Every partition of `n` is the partition of a permutation of `Fin n`. -/
theorem exists_perm_partition_eq {n : ℕ} (p : n.Partition) :
    ∃ σ : Equiv.Perm (Fin n), finPermPartition n σ = p := by
  let largeParts := p.parts.filter fun a => 2 ≤ a
  let unitParts := p.parts.filter fun a => ¬2 ≤ a
  have hsplit : largeParts + unitParts = p.parts := by
    exact Multiset.filter_add_not (p := fun a : ℕ => 2 ≤ a) p.parts
  have hunit : unitParts = Multiset.replicate unitParts.card 1 := by
    apply Multiset.eq_replicate_card.mpr
    intro a ha
    have ha' := Multiset.mem_filter.mp ha
    have hpos := p.parts_pos ha'.1
    omega
  have hunitSum : unitParts.sum = unitParts.card := by
    calc
      unitParts.sum = (Multiset.replicate unitParts.card 1).sum :=
        congrArg Multiset.sum hunit
      _ = unitParts.card := by
        rw [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one]
  have hsum : largeParts.sum + unitParts.card = n := by
    rw [← p.parts_sum, ← hsplit, Multiset.sum_add, hunitSum]
  have hlarge : largeParts.sum ≤ Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    omega
  have hlarge_mem : ∀ a ∈ largeParts, 2 ≤ a := by
    intro a ha
    exact (Multiset.mem_filter.mp ha).2
  obtain ⟨σ, hσ⟩ :=
    (Equiv.Perm.exists_with_cycleType_iff (Fin n)).mpr ⟨hlarge, hlarge_mem⟩
  refine ⟨σ, ?_⟩
  apply Nat.Partition.ext
  have hsupport : σ.support.card = largeParts.sum := by
    rw [← Equiv.Perm.sum_cycleType, hσ]
  have hremaining : n - largeParts.sum = unitParts.card := by
    omega
  rw [finPermPartition_parts, Equiv.Perm.parts_partition, hσ, Fintype.card_fin, hsupport,
    hremaining, ← hunit, hsplit]

/-- The partition of a conjugacy class of permutations. -/
def permConjClassPartition (n : ℕ) :
    ConjClasses (Equiv.Perm (Fin n)) → n.Partition :=
  Quotient.lift (finPermPartition n) fun σ τ h =>
    (finPermPartition_eq_iff n σ τ).mpr (Equiv.Perm.partition_eq_of_isConj.mp h)

/-- Taking the partition of the class of a permutation recovers its partition. -/
@[simp]
theorem permConjClassPartition_mk (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permConjClassPartition n (ConjClasses.mk σ) = finPermPartition n σ := by
  simp [permConjClassPartition, ConjClasses.mk]

/-- The partition distinguishes conjugacy classes of permutations. -/
theorem permConjClassPartition_injective (n : ℕ) :
    Function.Injective (permConjClassPartition n) := by
  intro C D h
  obtain ⟨σ, rfl⟩ := ConjClasses.exists_rep C
  obtain ⟨τ, rfl⟩ := ConjClasses.exists_rep D
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  apply (finPermPartition_eq_iff n σ τ).mp
  simpa only [permConjClassPartition_mk] using h

/-- Every partition is attained by a conjugacy class of permutations. -/
theorem permConjClassPartition_surjective (n : ℕ) :
    Function.Surjective (permConjClassPartition n) := by
  intro p
  obtain ⟨σ, hσ⟩ := exists_perm_partition_eq p
  exact ⟨ConjClasses.mk σ, by simpa using hσ⟩

/-- Partitions of `n` are equivalent to conjugacy classes of the symmetric group on `Fin n`. -/
noncomputable def partitionEquivConjClasses (n : ℕ) :
    n.Partition ≃ ConjClasses (Equiv.Perm (Fin n)) :=
  (Equiv.ofBijective (permConjClassPartition n)
    ⟨permConjClassPartition_injective n, permConjClassPartition_surjective n⟩).symm

/-- The conjugacy class associated to a partition has that partition. -/
@[simp]
theorem permConjClassPartition_partitionEquivConjClasses (n : ℕ) (p : n.Partition) :
    permConjClassPartition n (partitionEquivConjClasses n p) = p := by
  exact (partitionEquivConjClasses n).symm_apply_apply p

/-- The inverse class-to-partition map sends a representative to its permutation partition. -/
@[simp]
theorem partitionEquivConjClasses_symm_mk (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (partitionEquivConjClasses n).symm (ConjClasses.mk σ) = finPermPartition n σ := by
  rw [partitionEquivConjClasses, Equiv.symm_symm, Equiv.ofBijective_apply,
    permConjClassPartition_mk]

/-- The number of conjugacy classes of `Sₙ` is the number of partitions of `n`. -/
theorem card_conjClasses_perm_eq_card_partition (n : ℕ) :
    Fintype.card (ConjClasses (Equiv.Perm (Fin n))) = Fintype.card n.Partition :=
  Fintype.card_congr (partitionEquivConjClasses n).symm

end TauCeti
