/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Indicator sums over `Fin n` keyed by a natural number

`Fintype.sum_ite_eq` evaluates a sum whose indicator compares two elements of the index type.
When the comparison is instead between a natural number and the `Fin.val` of the index — as it is
whenever a family is indexed by `ℕ` and summed over `Fin n` — the index may fall outside the
range, so the value is a `dite` rather than a plain application.

## Main results

* `TauCeti.sum_ite_val_add`: a sum against the indicator of `b = k + j` picks out the summand at
  `b - j`, or vanishes when there is no such index.
-/

public section

namespace TauCeti

/-- **A shifted indicator picks out one summand.** Summing `f` over `Fin n` against the indicator
of `b = k + j` gives `f` at the index `b - j` when that is a valid index and `j ≤ b`, and `0`
otherwise. -/
theorem sum_ite_val_add {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) (b j : ℕ) :
    ∑ k : Fin n, (if b = (k : ℕ) + j then f k else 0)
      = if h : b - j < n ∧ j ≤ b then f ⟨b - j, h.1⟩ else 0 := by
  by_cases h : b - j < n ∧ j ≤ b
  · have hb : ∀ k : Fin n, (b = (k : ℕ) + j) = (k = (⟨b - j, h.1⟩ : Fin n)) := by
      intro k
      have := h.2
      simp only [Fin.ext_iff, eq_iff_iff]
      omega
    simp only [hb, dite_eq_left h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · rw [dite_eq_right h, Finset.sum_eq_zero]
    intro k _
    have := k.isLt
    exact ite_eq_right (by omega)

end TauCeti
