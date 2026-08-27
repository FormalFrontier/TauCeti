/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Range reindexing for finite sums

Generic identities for sums indexed by `Finset.range` and `Finset.Ioo`. These are used by the
coderivation/Taylor expansions, which reindex a cut-and-collapse double sum over a triangle to a
square and enlarge a vanishing-off-the-block range.

## Main results

* `sum_Ioo_eq_sum_range`: a sum over `Ioo 0 n` equals the sum over `range n` when the summand at
  `0` vanishes.
* `sum_range_triangle`: summing over pairs `(c, p - c)` with `c ≤ p < K` equals the square
  `range K × range K` when the family vanishes off the triangle.
* `sum_sum_range_eq_of_eq_zero_right`: enlarging both ranges of a double sum that vanishes outside
  a rectangle.
* `sum_range_add_add`: splitting a `range n` sum into a prefix, a block, and a suffix.
-/

public section

namespace TauCeti

open Finset

/-- Replacing a summation over `Finset.Ioo 0 n` by one over `Finset.range n`, provided the
summand at `0` vanishes. -/
theorem sum_Ioo_eq_sum_range {N : Type*} [AddCommMonoid N] (n : ℕ) (g : ℕ → N)
    (hg : g 0 = 0) : ∑ c ∈ Ioo 0 n, g c = ∑ c ∈ range n, g c := by
  refine sum_subset (fun c hc ↦ ?_) fun c hc hc' ↦ ?_
  · simp only [mem_Ioo, mem_range] at hc ⊢
    omega
  · simp only [mem_range] at hc
    have hc0 : c = 0 := by
      by_contra hne
      exact hc' (mem_Ioo.2 ⟨by omega, hc⟩)
    rw [hc0, hg]

/-- Summing a two-variable family over the pairs `(c, p - c)` with `c ≤ p < K` is the same as
summing it over the square `range K × range K`, when the family vanishes off the triangle. -/
theorem sum_range_triangle {N : Type*} [AddCommMonoid N] (K : ℕ) (g : ℕ → ℕ → N)
    (hg : ∀ c q : ℕ, K ≤ c + q → g c q = 0) :
    ∑ p ∈ range K, ∑ c ∈ range (p + 1), g c (p - c) =
      ∑ c ∈ range K, ∑ q ∈ range K, g c q := by
  rw [sum_range_diag_flip]
  refine sum_congr rfl fun c hc ↦ ?_
  simp only [mem_range] at hc
  exact sum_subset (range_subset_range.mpr (Nat.sub_le K c)) fun q _ hq ↦ by
    simp only [mem_range, not_lt] at hq
    exact hg c q (by omega)

/-- Enlarging both ranges of a double sum that vanishes for `b ≤ p` or `b < d`. -/
theorem sum_sum_range_eq_of_eq_zero_right {N : Type*} [AddCommMonoid N] {b K : ℕ} (hK : b ≤ K)
    (g : ℕ → ℕ → N) (hg : ∀ p d, b ≤ p ∨ b < d → g p d = 0) :
    ∑ p ∈ range b, ∑ d ∈ range (b + 1), g p d =
      ∑ p ∈ range K, ∑ d ∈ range (K + 1), g p d := by
  have inner : ∀ p : ℕ, ∑ d ∈ range (b + 1), g p d = ∑ d ∈ range (K + 1), g p d :=
    fun p ↦ sum_subset (range_subset_range.mpr (by omega)) fun d _ hd ↦ by
      simp only [mem_range, not_lt] at hd
      exact hg p d (Or.inr (by omega))
  have outer : ∑ p ∈ range b, ∑ d ∈ range (K + 1), g p d =
      ∑ p ∈ range K, ∑ d ∈ range (K + 1), g p d :=
    sum_subset (range_subset_range.mpr hK) fun p _ hp ↦ by
      simp only [mem_range, not_lt] at hp
      exact sum_eq_zero fun d _ ↦ hg p d (Or.inl hp)
  rw [← outer, ← sum_congr rfl fun p _ ↦ inner p]

/-- Splitting a sum over `range n` into a prefix of length `p`, a block of length `d`, and the
remaining suffix. -/
theorem sum_range_add_add {N : Type*} [AddCommMonoid N] (g : ℕ → N) {p d n : ℕ}
    (h : p + d ≤ n) :
    ∑ j ∈ range n, g j =
      (∑ j ∈ range p, g j) + (∑ j ∈ range d, g (p + j)) +
        ∑ j ∈ range (n - p - d), g (p + d + j) := by
  have s1 : ∑ j ∈ range n, g j =
      (∑ j ∈ range p, g j) + ∑ j ∈ range (n - p), g (p + j) := by
    have key := sum_range_add g p (n - p)
    rwa [show p + (n - p) = n from Nat.add_sub_cancel' (show p ≤ n from by omega)] at key
  have s2 : ∑ j ∈ range (n - p), g (p + j) =
      (∑ j ∈ range d, g (p + j)) + ∑ j ∈ range (n - p - d), g (p + d + j) := by
    have key := sum_range_add (f := fun k : ℕ => g (p + k)) d (n - p - d)
    rw [show d + (n - p - d) = n - p from by omega] at key
    refine key.trans ?_
    simp only [Nat.add_assoc]
  rw [s1, s2, ← add_assoc]

end TauCeti
