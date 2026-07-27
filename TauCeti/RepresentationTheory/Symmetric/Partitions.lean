/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
public import TauCeti.Combinatorics.Young.Partitions

/-!
# Partitions and conjugacy classes of permutations

This file gives the equivalence between partitions and conjugacy classes of permutations.  It is
proved for permutations of any finite type and specialized to `Equiv.Perm (Fin n)` for the roadmap
API.  Mathlib's partition of a permutation includes the fixed points as parts of size one.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 0.
-/

public section

namespace TauCeti

open Equiv

/-- Every partition of the cardinality of a finite type is the partition of a permutation. -/
theorem exists_perm_partition_eq {α : Type*} [Fintype α] [DecidableEq α]
    (p : (Fintype.card α).Partition) :
    ∃ σ : Equiv.Perm α, σ.partition = p := by
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
  have hsum : largeParts.sum + unitParts.card = Fintype.card α := by
    rw [← p.parts_sum, ← hsplit, Multiset.sum_add, hunitSum]
  have hlarge : largeParts.sum ≤ Fintype.card α := by omega
  have hlarge_mem : ∀ a ∈ largeParts, 2 ≤ a := by
    intro a ha
    exact (Multiset.mem_filter.mp ha).2
  obtain ⟨σ, hσ⟩ :=
    (Equiv.Perm.exists_with_cycleType_iff α).mpr ⟨hlarge, hlarge_mem⟩
  refine ⟨σ, ?_⟩
  apply Nat.Partition.ext
  have hsupport : σ.support.card = largeParts.sum := by
    rw [← Equiv.Perm.sum_cycleType, hσ]
  have hremaining : Fintype.card α - largeParts.sum = unitParts.card := by
    omega
  rw [Equiv.Perm.parts_partition, hσ, hsupport, hremaining, ← hunit, hsplit]

/-- The partition of a conjugacy class of permutations. -/
def permConjClassPartition {α : Type*} [Fintype α] [DecidableEq α] :
    ConjClasses (Equiv.Perm α) → (Fintype.card α).Partition :=
  Quotient.lift Equiv.Perm.partition fun _ _ h =>
    Equiv.Perm.partition_eq_of_isConj.mp h

/-- Taking the partition of the class of a permutation recovers its partition. -/
@[simp]
theorem permConjClassPartition_mk {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    permConjClassPartition (ConjClasses.mk σ) = σ.partition := by
  simp [permConjClassPartition, ConjClasses.mk]

/-- The partition distinguishes conjugacy classes of permutations. -/
theorem permConjClassPartition_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (permConjClassPartition (α := α)) := by
  intro C D h
  obtain ⟨σ, rfl⟩ := ConjClasses.exists_rep C
  obtain ⟨τ, rfl⟩ := ConjClasses.exists_rep D
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  simpa only [permConjClassPartition_mk] using h

/-- Every partition is attained by a conjugacy class of permutations. -/
theorem permConjClassPartition_surjective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Surjective (permConjClassPartition (α := α)) := by
  intro p
  obtain ⟨σ, hσ⟩ := exists_perm_partition_eq p
  exact ⟨ConjClasses.mk σ, by simpa using hσ⟩

/-- Partitions of the cardinality of a finite type are equivalent to conjugacy classes of its
permutations. -/
noncomputable def permEquivConjClasses (α : Type*) [Fintype α] [DecidableEq α] :
    (Fintype.card α).Partition ≃ ConjClasses (Equiv.Perm α) :=
  (Equiv.ofBijective (permConjClassPartition (α := α))
    ⟨permConjClassPartition_injective, permConjClassPartition_surjective⟩).symm

/-- Partitions of `n` are equivalent to conjugacy classes of the symmetric group on `Fin n`. -/
noncomputable def partitionEquivConjClasses (n : ℕ) :
    n.Partition ≃ ConjClasses (Equiv.Perm (Fin n)) :=
  (Equiv.cast (congrArg Nat.Partition (Fintype.card_fin n).symm)).trans
    (permEquivConjClasses (Fin n))

/-- The conjugacy class associated to a partition has that partition. -/
@[simp]
theorem permConjClassPartition_permEquivConjClasses (α : Type*) [Fintype α]
    [DecidableEq α] (p : (Fintype.card α).Partition) :
    permConjClassPartition (permEquivConjClasses α p) = p :=
  (permEquivConjClasses α).symm_apply_apply p

/-- The conjugacy class associated to a partition of `n` has that partition. -/
@[simp]
theorem permConjClassPartition_partitionEquivConjClasses (n : ℕ) (p : n.Partition) :
    permConjClassPartition (partitionEquivConjClasses n p) =
      Equiv.cast (congrArg Nat.Partition (Fintype.card_fin n).symm) p := by
  simp [partitionEquivConjClasses]

/-- The inverse class-to-partition map sends a representative to its permutation partition. -/
@[simp]
theorem permEquivConjClasses_symm_mk (α : Type*) [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    (permEquivConjClasses α).symm (ConjClasses.mk σ) = σ.partition := by
  rw [permEquivConjClasses, Equiv.symm_symm, Equiv.ofBijective_apply,
    permConjClassPartition_mk]

/-- The inverse class-to-partition map for `Fin n` sends a representative to its permutation
partition. -/
@[simp]
theorem partitionEquivConjClasses_symm_mk (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (partitionEquivConjClasses n).symm (ConjClasses.mk σ) =
      (Equiv.cast (congrArg Nat.Partition (Fintype.card_fin n).symm)).symm
        σ.partition := by
  simp [partitionEquivConjClasses]

/-- The number of conjugacy classes of permutations of a finite type is the number of partitions
of its cardinality. -/
theorem card_conjClasses_perm_eq_card_partition (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (ConjClasses (Equiv.Perm α)) =
      Fintype.card (Fintype.card α).Partition :=
  Fintype.card_congr (permEquivConjClasses α).symm

end TauCeti
