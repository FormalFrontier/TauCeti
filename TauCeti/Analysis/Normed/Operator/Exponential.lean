/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponentials of continuous linear endomorphisms

This file records basic facts about the exponential in the Banach algebra of continuous linear
endomorphisms of a real normed space.
-/

public section

open NormedSpace

namespace TauCeti

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace ContinuousLinearMap

/-- In the Banach algebra `X →L[ℝ] X`, the operator exponential is norm-bounded by the scalar
exponential of the norm: `‖exp x‖ ≤ Real.exp ‖x‖`. -/
theorem norm_exp_le_exp_norm (x : X →L[ℝ] X) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  rw [exp_eq_tsum ℝ]
  refine (norm_tsum_le_tsum_norm (norm_expSeries_summable' (𝕂 := ℝ) x)).trans ?_
  rw [Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  refine Summable.tsum_le_tsum (fun n => ?_) (norm_expSeries_summable' (𝕂 := ℝ) x)
    (expSeries_summable' (𝕂 := ℝ) ‖x‖)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), smul_eq_mul]
  gcongr
  cases n with
  | zero => simp only [pow_zero, ContinuousLinearMap.one_def]; exact ContinuousLinearMap.norm_id_le
  | succ m => exact norm_pow_le' x m.succ_pos

variable [CompleteSpace X]

/-- The operator exponential is additive on commuting elements of `X →L[ℝ] X`, phrased over the
scalar field `ℝ` (the `ℚ`-algebra instance required by `NormedSpace.exp_add_of_commute` is not
available here). -/
theorem exp_add_of_commute {x y : X →L[ℝ] X} (h : Commute x y) :
    exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    ((expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)

end ContinuousLinearMap

end TauCeti

end
