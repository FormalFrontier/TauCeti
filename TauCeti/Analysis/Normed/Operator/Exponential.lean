/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponentials in normed algebras

This file records basic facts about the exponential in normed algebras, including the
specialization to continuous linear endomorphisms of a real normed space.
-/

public section

open NormedSpace

namespace TauCeti

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- In a normed algebra whose unit has norm at most one, the exponential is norm-bounded by
the scalar exponential of the norm: `‖exp x‖ ≤ Real.exp ‖x‖`. -/
theorem norm_exp_le_exp_norm (h_one : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) :
    ‖exp x‖ ≤ Real.exp ‖x‖ := by
  rw [exp_eq_tsum ℚ]
  refine (norm_tsum_le_tsum_norm (norm_expSeries_summable' (𝕂 := ℚ) x)).trans ?_
  rw [Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  refine Summable.tsum_le_tsum (fun n => ?_) (norm_expSeries_summable' (𝕂 := ℚ) x)
    (expSeries_summable' (𝕂 := ℝ) ‖x‖)
  rw [norm_smul, ← Rat.norm_cast_real, Real.norm_eq_abs, Rat.cast_inv, Rat.cast_natCast,
    abs_of_nonneg (by positivity), smul_eq_mul]
  gcongr
  cases n with
  | zero => simpa only [pow_zero] using h_one
  | succ m => exact norm_pow_le' x m.succ_pos

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace ContinuousLinearMap

/-- The exponential of a real scalar multiple of the identity operator is the corresponding
scalar exponential times the identity. -/
@[simp]
theorem exp_smul_one (c : ℝ) :
    exp (c • (1 : X →L[ℝ] X)) = Real.exp c • 1 := by
  calc
    exp (c • (1 : X →L[ℝ] X)) = exp (algebraMap ℝ (X →L[ℝ] X) c) := by
      rw [Algebra.smul_def, mul_one]
    _ = algebraMap ℝ (X →L[ℝ] X) (exp c) := (algebraMap_exp_comm c).symm
    _ = Real.exp c • 1 := by
      rw [Real.exp_eq_exp_ℝ, Algebra.smul_def, mul_one]

/-- The norm of the exponential of a real scalar multiple of the identity operator is at most
the corresponding scalar exponential. -/
theorem norm_exp_smul_one_le (c : ℝ) :
    ‖exp (c • (1 : X →L[ℝ] X))‖ ≤ Real.exp c := by
  rw [exp_smul_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  simpa only [ContinuousLinearMap.one_def, mul_one] using
    mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (Real.exp_nonneg c)

end ContinuousLinearMap

end TauCeti

end
