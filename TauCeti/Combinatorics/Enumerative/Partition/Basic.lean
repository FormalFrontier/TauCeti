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
-/

public section

namespace TauCeti

namespace Nat.Partition

/-- A partition is equivalent to its decreasing list of positive parts. -/
@[expose] noncomputable def equivSortedParts (n : ℕ) :
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
theorem equivSortedParts_apply_parts (n : ℕ) (p : n.Partition) :
    (equivSortedParts n p).1 = p.parts.sort (· ≥ ·) := by
  simp [equivSortedParts]

/-- The inverse of `equivSortedParts` has the given list as its multiset of parts. -/
@[simp]
theorem equivSortedParts_symm_apply_parts (n : ℕ)
    (w : {w : List ℕ // (w.SortedGE ∧ ∀ x ∈ w, 0 < x) ∧ w.sum = n}) :
    ((equivSortedParts n).symm w).parts = w.1 := by
  simp [equivSortedParts]

end Nat.Partition

end TauCeti
