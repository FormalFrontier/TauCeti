/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Partitions as decreasing lists of positive parts

Mathlib's `Nat.Partition n` records the parts of a partition of `n` as a multiset.  This file
provides the equivalence `Nat.Partition.equivSortedParts` between partitions of `n` and weakly
decreasing lists of positive natural numbers summing to `n`, obtained by sorting the parts.

It also records the partition `Nat.Partition.ones n = (1ⁿ)` into `n` parts equal to `1`, the
opposite extreme to Mathlib's one-part `Nat.Partition.indiscrete n = (n)`.
-/

public section

namespace TauCeti

namespace Nat.Partition

/-- A partition is equivalent to its decreasing list of positive parts. -/
noncomputable def equivSortedParts (n : ℕ) :
    n.Partition ≃
      {w : List ℕ // (w.SortedGE ∧ ∀ x ∈ w, 0 < x) ∧ w.sum = n} where
  toFun p :=
    ⟨p.parts.sort (· ≥ ·),
      ⟨(Multiset.pairwise_sort p.parts (· ≥ ·)).sortedGE,
        fun x hx => p.parts_pos ((Multiset.mem_sort (r := (· ≥ ·))).mp hx)⟩, by
        rw [← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]⟩
  invFun w :=
    ⟨w.1, fun {_} hx => w.2.1.2 _ hx, by
      simpa only [Multiset.sum_coe] using w.2.2⟩
  left_inv p := by
    apply Nat.Partition.ext
    exact Multiset.sort_eq p.parts (· ≥ ·)
  right_inv w := by
    apply Subtype.ext
    exact List.Perm.eq_of_sortedGE
      (Multiset.pairwise_sort (↑w.1 : Multiset ℕ) (· ≥ ·)).sortedGE w.2.1.1
      (Multiset.coe_eq_coe.mp (Multiset.sort_eq (↑w.1 : Multiset ℕ) (· ≥ ·)))

/-- Sorting the parts is the forward map of `equivSortedParts`. -/
@[simp]
theorem equivSortedParts_apply_coe (n : ℕ) (p : n.Partition) :
    (equivSortedParts n p).1 = p.parts.sort (· ≥ ·) := by
  simp [equivSortedParts]

/-- The inverse of `equivSortedParts` has the given list as its multiset of parts. -/
@[simp]
theorem equivSortedParts_symm_apply_parts (n : ℕ)
    (w : {w : List ℕ // (w.SortedGE ∧ ∀ x ∈ w, 0 < x) ∧ w.sum = n}) :
    ((equivSortedParts n).symm w).parts = w.1 := by
  simp [equivSortedParts]

/-- The partition `(1ⁿ)` of `n` into `n` parts, each equal to `1`.

This is the finest partition of `n`, opposite to Mathlib's coarsest `Nat.Partition.indiscrete n`,
which has the single part `n`.

The parts are exposed only through `Nat.Partition.ones_parts`. -/
def ones (n : ℕ) : n.Partition where
  parts := Multiset.replicate n 1
  parts_pos hi := by simp [Multiset.eq_of_mem_replicate hi]
  parts_sum := by simp

@[simp]
theorem ones_parts (n : ℕ) : (ones n).parts = Multiset.replicate n 1 := by simp [ones]

/-- The product of the factorials of the parts of `(1ⁿ)` is `1`. -/
theorem prod_map_factorial_ones (n : ℕ) :
    ((ones n).parts.map Nat.factorial).prod = 1 := by
  simp [Multiset.map_replicate]

/-- The product of the factorials of the parts of the one-part partition `(n)` is `n !`. -/
@[simp]
theorem prod_map_factorial_indiscrete (n : ℕ) :
    ((_root_.Nat.Partition.indiscrete n).parts.map Nat.factorial).prod = n.factorial := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [_root_.Nat.Partition.indiscrete_parts hn.ne']

end Nat.Partition

end TauCeti
