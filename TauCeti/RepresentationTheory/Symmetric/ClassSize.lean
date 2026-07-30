/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Perm.Centralizer
public import TauCeti.RepresentationTheory.Symmetric.Partitions

/-!
# Conjugacy class sizes in the symmetric group

The conjugacy classes of `Equiv.Perm α` are indexed by partitions of `Fintype.card α` through
`Equiv.Perm.partition`.  This file computes the size of each class.  The weight attached to a
partition `μ` is

`zPart μ = ∏ i, i ^ mᵢ * mᵢ !`,

where `mᵢ` is the multiplicity of the part `i` in `μ`, that is, Mathlib's `μ.parts.count i`; no
separate multiplicity function is introduced.  It is the order of the centralizer of any
permutation with partition `μ`, so the class of such a permutation has `n ! / zPart μ` elements.

The main results are `nat_card_centralizer_eq_zPart`, the multiplicative class-size formula
`card_partition_mul_zPart` with its transported form `card_partition_parts_mul_zPart_fin`, and the
normalisation `sum_factorial_div_zPart`, which says the class sizes add up to `n !`.  These are the
weights in the orthogonality relations for the characters of the symmetric group, where the class
with partition `μ` is weighted by `1 / zPart μ`.

Mathlib counts permutations of a given *cycle type*, a multiset recording only the cycles of length
at least two (`Equiv.Perm.nat_card_centralizer`, `Equiv.Perm.card_isConj_mul_eq`).  The translation
to partitions, which record the fixed points as parts equal to one, is `zPart_partition`.

Partitions of `Fintype.card α` and of `n` are different types even when `Fintype.card α = n`, so
the statements about `Equiv.Perm (Fin n)` describe the permutations with partition `μ` by the
equality `σ.partition.parts = μ.parts` of the underlying multisets, which determines the partition.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 6, the class-sizes build item.
* Mathlib's `Mathlib.GroupTheory.Perm.Centralizer`, for the cycle-type count.
-/

public section

namespace TauCeti

open Equiv Nat

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The weight `z_μ = ∏ᵢ i ^ mᵢ · mᵢ !` of a partition `μ`, where `mᵢ = μ.parts.count i` is the
multiplicity of the part `i`.

It is the order of the centralizer of a permutation whose cycle lengths are the parts of `μ`, so
the conjugacy class of that permutation has `n ! / zPart μ` elements. -/
def zPart {n : ℕ} (μ : n.Partition) : ℕ :=
  ∏ i ∈ μ.parts.toFinset, i ^ μ.parts.count i * (μ.parts.count i)!

/-- The weight depends only on the multiset of parts, so it is unchanged by transporting a
partition along an equality of the number being partitioned. -/
theorem zPart_congr {m n : ℕ} {μ : m.Partition} {ν : n.Partition} (h : μ.parts = ν.parts) :
    zPart μ = zPart ν := by
  simp only [zPart, h]

/-- The defining product may be taken over any finite set of naturals containing the parts: the
extra factors are `i ^ 0 * 0 ! = 1`. -/
theorem zPart_eq_prod_of_subset {n : ℕ} (μ : n.Partition) {s : Finset ℕ}
    (hs : μ.parts.toFinset ⊆ s) :
    zPart μ = ∏ i ∈ s, i ^ μ.parts.count i * (μ.parts.count i)! := by
  refine Finset.prod_subset hs fun i _ hi => ?_
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hi)]
  simp

/-- The defining equation of `zPart`: the product of `i ^ mᵢ * mᵢ !` over the parts `i` of `μ`,
the case `s = μ.parts.toFinset` of `zPart_eq_prod_of_subset`. -/
theorem zPart_def {n : ℕ} (μ : n.Partition) :
    zPart μ = ∏ i ∈ μ.parts.toFinset, i ^ μ.parts.count i * (μ.parts.count i)! :=
  zPart_eq_prod_of_subset μ Finset.Subset.rfl

/-- The weight of a partition is positive; the parts of a partition are positive. -/
theorem zPart_pos {n : ℕ} (μ : n.Partition) : 0 < zPart μ := by
  refine Finset.prod_pos fun i hi => ?_
  have hi' : 0 < i := μ.parts_pos (Multiset.mem_toFinset.mp hi)
  positivity

/-- The weight of the one-part partition of `n` is `n`: for `2 ≤ n` an `n`-cycle commutes exactly
with its own powers, and for `n = 1` the centralizer is the trivial group. -/
@[simp]
theorem zPart_indiscrete {n : ℕ} (hn : n ≠ 0) : zPart (Nat.Partition.indiscrete n) = n := by
  simp [zPart, Nat.Partition.indiscrete_parts hn]

/-- The weight of the partition of a permutation, in terms of its cycle type.

Mathlib's cycle type omits the fixed points; they contribute the single extra factor `1 ^ k * k !`,
where `k` is the number of fixed points. -/
theorem zPart_partition (σ : Equiv.Perm α) :
    zPart σ.partition =
      (Fintype.card α - σ.cycleType.sum)! * σ.cycleType.prod *
        ∏ i ∈ σ.cycleType.toFinset, (σ.cycleType.count i)! := by
  set m := σ.cycleType with hm
  set k := Fintype.card α - σ.support.card with hk
  have hparts : σ.partition.parts = m + Multiset.replicate k 1 := Equiv.Perm.parts_partition
  have h1 : (1 : ℕ) ∉ m := fun h => by simpa using Equiv.Perm.two_le_of_mem_cycleType h
  have hsub : σ.partition.parts.toFinset ⊆ insert 1 m.toFinset := by
    intro i hi
    rw [Multiset.mem_toFinset, hparts, Multiset.mem_add] at hi
    rcases hi with h | h
    · exact Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr h)
    · exact Finset.mem_insert.mpr (Or.inl (Multiset.eq_of_mem_replicate h))
  have hcount : ∀ i ∈ m.toFinset, σ.partition.parts.count i = m.count i := by
    intro i hi
    have hne : (1 : ℕ) ≠ i := fun h => h1 (h ▸ Multiset.mem_toFinset.mp hi)
    rw [hparts, Multiset.count_add, Multiset.count_replicate, if_neg hne, add_zero]
  have hcount_one : σ.partition.parts.count 1 = k := by
    rw [hparts, Multiset.count_add, Multiset.count_eq_zero_of_notMem h1,
      Multiset.count_replicate_self, zero_add]
  rw [zPart_eq_prod_of_subset σ.partition hsub,
    Finset.prod_insert (by simpa using h1), hcount_one,
    Finset.prod_congr rfl (fun i hi => by rw [hcount i hi]), Finset.prod_mul_distrib,
    ← Finset.prod_multiset_count, one_pow, one_mul, hk, Equiv.Perm.sum_cycleType]
  ring

/-- The centralizer of a permutation has order the weight of its partition. -/
theorem nat_card_centralizer_eq_zPart (σ : Equiv.Perm α) :
    Nat.card (Subgroup.centralizer {σ}) = zPart σ.partition := by
  rw [zPart_partition, Equiv.Perm.nat_card_centralizer]

/-- The class-size formula in its conjugacy formulation: the conjugacy class of `σ` has
`(Fintype.card α)! / zPart σ.partition` elements. -/
theorem card_isConj_mul_zPart (σ : Equiv.Perm α) :
    Nat.card {τ : Equiv.Perm α | IsConj σ τ} * zPart σ.partition = (Fintype.card α)! := by
  rw [zPart_partition]
  exact Equiv.Perm.card_isConj_mul_eq σ

/-- The class-size formula: the permutations with partition `μ` number
`(Fintype.card α)! / zPart μ`.

Stated multiplicatively, so it carries no divisibility obligation; the quotient form is
`card_partition_parts_fin`. -/
theorem card_partition_mul_zPart (μ : (Fintype.card α).Partition) :
    Nat.card {σ : Equiv.Perm α // σ.partition = μ} * zPart μ = (Fintype.card α)! := by
  obtain ⟨g, hg⟩ := exists_perm_partition_eq μ
  have hcongr : Nat.card {σ : Equiv.Perm α // σ.partition = μ} =
      Nat.card {τ : Equiv.Perm α | IsConj g τ} :=
    Nat.card_congr <| Equiv.subtypeEquivRight fun τ => by
      rw [Set.mem_setOf_eq, Equiv.Perm.partition_eq_of_isConj, hg, eq_comm]
  rw [hcongr, ← hg]
  exact card_isConj_mul_zPart g

/-- The class-size formula transported along an equality `Fintype.card α = n`. -/
theorem card_partition_parts_mul_zPart {n : ℕ} (h : Fintype.card α = n) (μ : n.Partition) :
    Nat.card {σ : Equiv.Perm α // σ.partition.parts = μ.parts} * zPart μ = n ! := by
  subst h
  have hfib : {σ : Equiv.Perm α // σ.partition.parts = μ.parts} =
      {σ : Equiv.Perm α // σ.partition = μ} := by
    congr 1 with σ
    exact ⟨Nat.Partition.ext, fun hσ => by rw [hσ]⟩
  rw [hfib]
  exact card_partition_mul_zPart μ

/-- The class-size formula for `Equiv.Perm (Fin n)`, the form the roadmap states: the permutations
with partition `μ` number `n ! / zPart μ`. -/
theorem card_partition_parts_mul_zPart_fin (n : ℕ) (μ : n.Partition) :
    Nat.card {σ : Equiv.Perm (Fin n) // σ.partition.parts = μ.parts} * zPart μ = n ! :=
  card_partition_parts_mul_zPart (Fintype.card_fin n) μ

/-- The weight of a partition of `n` divides `n !`. -/
theorem zPart_dvd_factorial {n : ℕ} (μ : n.Partition) : zPart μ ∣ n ! :=
  ⟨_, ((card_partition_parts_mul_zPart_fin n μ).symm.trans (mul_comm _ _))⟩

/-- The quotient form of the class-size formula: the permutations with partition `μ` number
`(Fintype.card α)! / zPart μ`. -/
theorem card_partition_div_zPart (μ : (Fintype.card α).Partition) :
    Nat.card {σ : Equiv.Perm α // σ.partition = μ} = (Fintype.card α)! / zPart μ :=
  (Nat.div_eq_of_eq_mul_left (zPart_pos μ) (card_partition_mul_zPart μ).symm).symm

/-- The quotient form of the class-size formula, transported along an equality
`Fintype.card α = n`. -/
theorem card_partition_parts_div_zPart {n : ℕ} (h : Fintype.card α = n) (μ : n.Partition) :
    Nat.card {σ : Equiv.Perm α // σ.partition.parts = μ.parts} = n ! / zPart μ :=
  (Nat.div_eq_of_eq_mul_left (zPart_pos μ) (card_partition_parts_mul_zPart h μ).symm).symm

/-- The quotient form of the class-size formula for `Equiv.Perm (Fin n)`. -/
theorem card_partition_parts_fin (n : ℕ) (μ : n.Partition) :
    Nat.card {σ : Equiv.Perm (Fin n) // σ.partition.parts = μ.parts} = n ! / zPart μ :=
  card_partition_parts_div_zPart (Fintype.card_fin n) μ

/-- The permutations of `α` whose partition is the one-part partition of `n = Fintype.card α`
number `(n - 1)!`.

For `2 ≤ n` these are the `n`-cycles.  For `n ≤ 1` the fibre is the identity alone and both sides
are `1`, but the identity is not a cycle in Mathlib's sense: the one-part partition of `0` has no
parts, and that of `1` has the single part `1`, which is the partition of the identity of a
one-element type. -/
theorem card_partition_parts_indiscrete {n : ℕ} (h : Fintype.card α = n) :
    Nat.card {σ : Equiv.Perm α //
      σ.partition.parts = (Nat.Partition.indiscrete n).parts} = (n - 1)! := by
  rw [card_partition_parts_div_zPart h]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zPart_def]
  · rw [zPart_indiscrete hn]
    exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hn)
      (by rw [mul_comm, Nat.mul_factorial_pred hn])

/-- There are `(n - 1)!` `n`-cycles in `Equiv.Perm (Fin n)` when `2 ≤ n`; for `n ≤ 1` the fibre is
the identity permutation of `Fin n`, which is not a cycle, and both sides are `1`. -/
theorem card_partition_parts_indiscrete_fin (n : ℕ) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      σ.partition.parts = (Nat.Partition.indiscrete n).parts} = (n - 1)! :=
  card_partition_parts_indiscrete (Fintype.card_fin n)

/-- The permutations of a finite type are partitioned by their partitions. -/
theorem sum_card_partition (α : Type*) [Fintype α] [DecidableEq α] :
    ∑ μ : (Fintype.card α).Partition, Nat.card {σ : Equiv.Perm α // σ.partition = μ} =
      (Fintype.card α)! := by
  classical
  have h : Nat.card (Σ μ : (Fintype.card α).Partition, {σ : Equiv.Perm α // σ.partition = μ}) =
      Nat.card (Equiv.Perm α) :=
    Nat.card_congr (Equiv.sigmaFiberEquiv _)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_sigma,
    Fintype.card_perm] at h
  simpa [Nat.card_eq_fintype_card] using h

/-- The fibre decomposition transported along an equality `Fintype.card α = n`. -/
theorem sum_card_partition_parts {n : ℕ} (α : Type*) [Fintype α] [DecidableEq α]
    (h : Fintype.card α = n) :
    ∑ μ : n.Partition, Nat.card {σ : Equiv.Perm α // σ.partition.parts = μ.parts} = n ! := by
  subst h
  refine Eq.trans (Finset.sum_congr rfl fun μ _ => ?_) (sum_card_partition α)
  exact Nat.card_congr <| Equiv.subtypeEquivRight fun σ =>
    ⟨Nat.Partition.ext, fun hσ => by rw [hσ]⟩

/-- The class sizes add up to the order of the group.  Every division here is exact, by
`zPart_dvd_factorial`.

This is the natural-number form of the normalisation of the orthogonality weights; the rational
identity `∑_μ 1 / z_μ = 1`, which divides this one by `n !`, is not formalised here. -/
theorem sum_factorial_div_zPart (n : ℕ) : ∑ μ : n.Partition, n ! / zPart μ = n ! :=
  Eq.trans (Finset.sum_congr rfl fun μ _ => (card_partition_parts_fin n μ).symm)
    (sum_card_partition_parts (Fin n) (Fintype.card_fin n))

end TauCeti
