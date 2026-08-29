/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.End

import Mathlib.Tactic.FinCases

/-!
# Basic results about finite ordinal types

This file collects elementary facts about finite ordinal types, including the classification of
permutations of `Fin 2` and indicator sums indexed by `Fin n`.

`Fintype.sum_ite_eq` evaluates a sum whose indicator compares two elements of the index type.
When the comparison is instead between a natural number and the `Fin.val` of the index — as it is
whenever a family is indexed by `ℕ` and summed over `Fin n` — the index may fall outside the
range, so the value is a `dite` rather than a plain application.

## Main results

* `TauCeti.perm_fin_two_eq_one_or_swap`: every permutation of `Fin 2` is the identity or the
  transposition.
* `TauCeti.sum_ite_val_add`: a sum against the indicator of `b = k + j` picks out the summand at
  `b - j`, or vanishes when there is no such index.
-/

public section

namespace TauCeti

/-- A permutation of `Fin 2` is either the identity or the transposition. -/
theorem perm_fin_two_eq_one_or_swap (e : Equiv.Perm (Fin 2)) :
    e = 1 ∨ e = Equiv.swap 0 1 := by
  by_cases h0 : e 0 = 0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · apply Fin.eq_one_of_ne_zero
      intro h1
      exact Fin.zero_ne_one (e.injective (h1.trans h0.symm)).symm
  · right
    have h0' : e 0 = 1 := Fin.eq_one_of_ne_zero _ h0
    apply Equiv.ext
    intro i
    fin_cases i
    · simpa using h0'
    · have h1 : e 1 = 0 := by
        by_contra h
        have h1' : e 1 = 1 := Fin.eq_one_of_ne_zero _ h
        exact Fin.zero_ne_one (e.injective (h1'.trans h0'.symm)).symm
      simpa using h1

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
