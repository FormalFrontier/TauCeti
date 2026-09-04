/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounds for falling factorials

These estimates compare powers with the falling factorials that count ordered injections.
-/

public section

namespace TauCeti

/-- The real falling product never exceeds the corresponding power. -/
theorem falling_prod_le_pow (n k : ℕ) :
    ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ)) ≤ (n : ℝ) ^ k := by
  rw [← descPochhammer_eval_eq_prod_range,
    descPochhammer_eval_eq_descFactorial]
  exact_mod_cast Nat.descFactorial_le_pow n k

/-- The shortfall of the real falling product against the power is bounded by the quadratic
collision term times the preceding power. -/
theorem pow_sub_falling_prod_le (n k : ℕ) :
    (n : ℝ) ^ k - ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ))
      ≤ ((k.choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by
  induction k with
  | zero =>
    have hc0 : Nat.choose 0 2 = 0 := by decide
    simp [hc0]
  | succ k ih =>
    have hP := falling_prod_le_pow n k
    have hchooseR : (((k + 1).choose 2 : ℕ) : ℝ)
        = ((k.choose 2 : ℕ) : ℝ) + (k : ℝ) := by
      have h := Nat.choose_succ_succ' k 1
      rw [Nat.choose_one_right] at h
      have h2 : (k + 1).choose 2 = k.choose 2 + k := h.trans (add_comm _ _)
      rw [h2]
      push_cast
      ring
    rw [Finset.prod_range_succ]
    by_cases hk0 : k = 0
    · subst hk0
      have hc0 : (0 + 1).choose 2 = 0 :=
        Nat.choose_eq_zero_of_lt (by decide)
      rw [hc0]
      simp
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hpow : (n : ℝ) ^ (k - 1) * (n : ℝ) = (n : ℝ) ^ k := by
        have hps := pow_succ (n : ℝ) (k - 1)
        rw [Nat.sub_add_cancel hk1] at hps
        exact hps.symm
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have hkk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      calc (n : ℝ) ^ (k + 1)
            - (∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ))) * ((n : ℝ) - (k : ℝ))
          = (n : ℝ) * ((n : ℝ) ^ k - ∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ)))
            + (k : ℝ) * (∏ i ∈ Finset.range k, ((n : ℝ) - (i : ℝ))) := by ring
        _ ≤ (n : ℝ) * (((k.choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k - 1))
            + (k : ℝ) * (n : ℝ) ^ k := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left ih hnn
              · exact mul_le_mul_of_nonneg_left hP hkk
        _ = (((k + 1).choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k + 1 - 1) := by
              rw [hchooseR, Nat.add_sub_cancel, ← hpow]
              ring

/-- The shortfall of the falling factorial against the power is bounded by the quadratic
collision term times the preceding power. -/
theorem pow_sub_descFactorial_le (n k : ℕ) :
    (n : ℝ) ^ k - (n.descFactorial k : ℝ)
      ≤ ((k.choose 2 : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by
  rw [← descPochhammer_eval_eq_descFactorial ℝ n k,
    descPochhammer_eval_eq_prod_range]
  exact pow_sub_falling_prod_le n k

end TauCeti
