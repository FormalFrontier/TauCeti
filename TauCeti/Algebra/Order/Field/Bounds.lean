/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A bound for differences of normalized quantities

The main result bounds the difference of two nonnegative quantities after normalization by
possibly different nonnegative denominators.
-/

public section

namespace TauCeti

/-- Two fractions with different denominators are close when their numerators differ by at most
the denominators' gap. -/
theorem abs_div_sub_div_le (a b N M : ℝ) (hN : 0 < N)
    (ha : 0 ≤ a) (haN : a ≤ N) (hb : 0 ≤ b) (hbM : b ≤ M) (hM : 0 ≤ M)
    (hMN : M ≤ N) (hba : b ≤ a) (hab : a - b ≤ N - M) :
    |a / N - b / M| ≤ (N - M) / N := by
  by_cases hM0 : M = 0
  · subst hM0
    have hb0 : b = 0 := le_antisymm hbM hb
    simp only [hb0, zero_div, sub_zero, div_self (ne_of_gt hN),
      abs_of_nonneg (div_nonneg ha (le_of_lt hN))]
    exact div_le_one_of_le₀ haN (le_of_lt hN)
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    have hNM : 0 < N * M := mul_pos hN hMpos
    have hN' : N ≠ 0 := ne_of_gt hN
    have hM' : M ≠ 0 := ne_of_gt hMpos
    have h1 : (a - b) * M ≤ (N - M) * M := mul_le_mul_of_nonneg_right hab hM
    have h2 : 0 ≤ b * (N - M) := mul_nonneg hb (sub_nonneg.mpr hMN)
    have h3 : b * (N - M) ≤ M * (N - M) :=
      mul_le_mul_of_nonneg_right hbM (sub_nonneg.mpr hMN)
    have h4 : (b - a) * M ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hba) hM
    have hub : a * M - b * N ≤ M * (N - M) := by linarith [h1, h2]
    have hlb : -(M * (N - M)) ≤ a * M - b * N := by linarith [h3, h4]
    have habs : |a * M - b * N| ≤ M * (N - M) := abs_le.mpr ⟨hlb, hub⟩
    have hNM' : N * M ≠ 0 := mul_ne_zero hN' hM'
    have e1 : a / N = (a * M) / (N * M) := by
      rw [div_eq_div_iff hN' hNM']
      ring
    have e2 : b / M = (b * N) / (N * M) := by
      rw [div_eq_div_iff hM' hNM']
      ring
    have hdiv : a / N - b / M = (a * M - b * N) / (N * M) := by
      rw [e1, e2, ← sub_div]
    rw [hdiv, abs_div, abs_of_pos hNM]
    calc |a * M - b * N| / (N * M) ≤ M * (N - M) / (N * M) :=
            div_le_div_of_nonneg_right habs (le_of_lt hNM)
      _ = (N - M) / N := by
            rw [div_eq_div_iff (mul_ne_zero hN' hM') hN']
            ring

end TauCeti
