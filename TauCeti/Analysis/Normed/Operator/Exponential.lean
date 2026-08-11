/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Exponentials in normed algebras

This file records basic facts about the exponential in normed algebras, including the
specialization to continuous linear endomorphisms of a real normed space: the norm bound
`‖exp x‖ ≤ Real.exp ‖x‖`, exponential bounds for power-bounded operators, the exponential of a
scalar multiple of the identity, and the Duhamel identity
`exp (t • B) x - x = ∫₀ᵗ exp (u • B) (B x) du` for the orbits of a bounded operator.
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

/-- If every power of a bounded operator `B` has norm at most `M`, then
`‖exp (s B)‖ ≤ M exp s` for every `s ≥ 0`. -/
theorem norm_exp_smul_le_mul_exp_of_norm_pow_le [CompleteSpace X] {B : X →L[ℝ] X} {M s : ℝ}
    (hs : 0 ≤ s) (hpow : ∀ n : ℕ, ‖B ^ n‖ ≤ M) :
    ‖exp (s • B)‖ ≤ M * Real.exp s := by
  have hseries : HasSum
      (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (s • B) ^ n) (exp (s • B)) :=
    NormedSpace.exp_series_hasSum_exp' (s • B)
  have hscalar : HasSum (fun n : ℕ => M * (s ^ n / n.factorial))
      (M * Real.exp s) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [div_eq_mul_inv, mul_comm] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) s).mul_left M
  have hterm (n : ℕ) :
      ‖((n.factorial : ℝ)⁻¹) • (s • B) ^ n‖ ≤ M * (s ^ n / n.factorial) := by
    rw [smul_pow, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), abs_pow, abs_of_nonneg hs]
    calc
      (n.factorial : ℝ)⁻¹ * (s ^ n * ‖B ^ n‖)
          ≤ (n.factorial : ℝ)⁻¹ * (s ^ n * M) := by
            gcongr
            exact hpow n
      _ = M * (s ^ n / n.factorial) := by
        rw [div_eq_mul_inv]
        ring
  exact hseries.norm_le_of_bounded hscalar hterm

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

/-- **The Duhamel identity for the exponential of a bounded operator.** For `B : X →L[ℝ] X`,
`exp (t B) x - x = ∫₀ᵗ exp (u B) (B x) du`.

This is the fundamental theorem of calculus applied to the differentiable orbit
`u ↦ exp (u B) x`, whose derivative is the continuous function `u ↦ exp (u B) (B x)`. -/
theorem exp_smul_apply_sub_eq_intervalIntegral [CompleteSpace X] (B : X →L[ℝ] X) (t : ℝ) (x : X) :
    exp (t • B) x - x = ∫ u in (0 : ℝ)..t, exp (u • B) (B x) := by
  have hderiv : ∀ u : ℝ, HasDerivAt (fun v : ℝ => exp (v • B) x) (exp (u • B) (B x)) u := by
    intro u
    simpa [mul_apply_eq_comp] using
      (hasDerivAt_exp_smul_const B u).clm_apply (hasDerivAt_const u x)
  have hcont : Continuous fun u : ℝ => exp (u • B) (B x) :=
    (differentiable_exp_smul_const ℝ B).continuous.clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont.intervalIntegrable 0 t)]
  simp

end ContinuousLinearMap

end TauCeti

end
