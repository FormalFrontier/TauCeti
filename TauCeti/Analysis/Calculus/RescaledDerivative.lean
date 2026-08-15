/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Rescaled derivative limits

This file records the normed-space limit obtained by sampling a differentiable curve at `t / n`
and multiplying its value by `n`.

## Main result

* `tendsto_nsmul_apply_div_of_hasDerivAt`: a curve through zero with derivative `f'` satisfies
  `n • f (t / n) → t • f'`.
-/

public section

open Filter

/-- If `f` passes through zero with derivative `f'`, then `n • f (t / n)` tends to `t • f'`. -/
theorem tendsto_nsmul_apply_div_of_hasDerivAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} (hf : HasDerivAt f f' 0) (hf0 : f 0 = 0) (t : ℝ) :
    Tendsto (fun n : ℕ => n • f (t / n)) atTop (nhds (t • f')) := by
  by_cases ht : t = 0
  · subst t
    simpa only [zero_div, hf0, nsmul_zero, zero_smul] using tendsto_const_nhds
  have hs : Tendsto (fun n : ℕ => t / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat t
  have hs_ne : ∀ᶠ n : ℕ in (atTop : Filter ℕ), t / (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hnpos
    exact div_ne_zero ht (show (n : ℝ) ≠ 0 from
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos))
  have hs' : Tendsto (fun n : ℕ => t / (n : ℝ)) atTop
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs, hs_ne⟩
  have hscaled := (hf.tendsto_slope_zero.comp hs').const_smul t
  convert hscaled using 1
  funext n
  by_cases hn0 : n = 0
  · subst n
    simp [hf0]
  rw [show n • f (t / (n : ℝ)) = (n : ℝ) • f (t / (n : ℝ)) by
    exact (Nat.cast_smul_eq_nsmul ℝ n _).symm]
  simp only [Function.comp_apply, zero_add, hf0, sub_zero]
  rw [smul_smul]
  congr 1
  field_simp

end
