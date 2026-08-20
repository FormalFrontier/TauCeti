/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Moments and moment-generating function of the Poisson distribution

This file develops the elementary analytic API of the real-valued Poisson law. For a rate
`r : ℝ≥0`, the cast law `Po(ℝ, r)` has all exponential moments, moment-generating function
`exp (r * (exp t - 1))`, cumulant-generating function `r * (exp t - 1)`, and both mean and
variance equal to `r`.

The series calculation for the moment-generating function follows the calculation of
`ProbabilityTheory.charFun_map_cast_poissonMeasure` in Mathlib. The moment formulas are then
obtained by differentiating the moment-generating function.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal Nat

namespace TauCeti

/-- The moment-generating function of a real-valued Poisson law of rate `r` is
`t ↦ exp (r * (exp t - 1))`. -/
theorem mgf_id_map_cast_poissonMeasure (r : ℝ≥0) :
    mgf (fun x : ℝ ↦ x) Po(ℝ, r) = fun t ↦ exp ((r : ℝ) * (exp t - 1)) := by
  ext t
  rw [mgf, integral_map .of_discrete (by fun_prop), integral_poissonMeasure r]
  simp only [smul_eq_mul]
  calc
    ∑' n, (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) * exp (t * (n : ℝ))
        = ∑' n, exp (-(r : ℝ)) * (((r : ℝ) * exp t) ^ n / n !) := by
            congr with n
            rw [mul_pow, ← exp_nat_mul]
            ring_nf
    _ = exp (-(r : ℝ)) * ∑' n, ((r : ℝ) * exp t) ^ n / n ! := tsum_mul_left
    _ = exp (-(r : ℝ)) * exp ((r : ℝ) * exp t) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * exp t)).tsum_eq, exp_eq_exp_ℝ]
    _ = exp ((r : ℝ) * (exp t - 1)) := by
      rw [← exp_add]
      ring_nf

/-- Every exponential moment of a real-valued Poisson law is integrable. -/
theorem integrable_exp_mul_id_map_cast_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) Po(ℝ, r) := by
  rw [← mgf_pos_iff, mgf_id_map_cast_poissonMeasure]
  exact exp_pos _

/-- The exponential-integrability domain of a real-valued Poisson law is all of `ℝ`. -/
@[simp]
theorem integrableExpSet_id_map_cast_poissonMeasure (r : ℝ≥0) :
    integrableExpSet (fun x : ℝ ↦ x) Po(ℝ, r) = Set.univ := by
  ext t
  simpa [integrableExpSet] using integrable_exp_mul_id_map_cast_poissonMeasure r t

/-- The cumulant-generating function of a real-valued Poisson law of rate `r` is
`t ↦ r * (exp t - 1)`. -/
theorem cgf_id_map_cast_poissonMeasure (r : ℝ≥0) :
    cgf (fun x : ℝ ↦ x) Po(ℝ, r) = fun t ↦ (r : ℝ) * (exp t - 1) := by
  ext t
  rw [cgf, mgf_id_map_cast_poissonMeasure, log_exp]

/-- The mean of a real-valued Poisson law is its rate. -/
@[simp]
theorem integral_id_map_cast_poissonMeasure (r : ℝ≥0) :
    ∫ x, x ∂Po(ℝ, r) = r := by
  have hzero : 0 ∈ interior (integrableExpSet (fun x : ℝ ↦ x) Po(ℝ, r)) := by simp
  rw [← deriv_mgf_zero hzero, mgf_id_map_cast_poissonMeasure,
    _root_.deriv_exp (by fun_prop)]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_fun_sub (by fun_prop) (by fun_prop)]
  simp

/-- The second raw moment of a real-valued Poisson law is `r ^ 2 + r`. -/
@[simp]
theorem integral_sq_map_cast_poissonMeasure (r : ℝ≥0) :
    ∫ x, x ^ 2 ∂Po(ℝ, r) = (r : ℝ) ^ 2 + r := by
  calc
    ∫ x, x ^ 2 ∂Po(ℝ, r) = iteratedDeriv 2 (mgf (fun x : ℝ ↦ x) Po(ℝ, r)) 0 := by
      simpa only [Pi.pow_apply] using (iteratedDeriv_mgf_zero (by simp) 2).symm
    _ = (r : ℝ) ^ 2 + r := by
      rw [mgf_id_map_cast_poissonMeasure, iteratedDeriv_succ, iteratedDeriv_one]
      have hderiv : deriv (fun t : ℝ ↦ exp ((r : ℝ) * (exp t - 1))) =
          fun t ↦ (r : ℝ) * exp t * exp ((r : ℝ) * (exp t - 1)) := by
        ext t
        rw [_root_.deriv_exp (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop),
          deriv_fun_sub (by fun_prop) (by fun_prop)]
        simp only [deriv_const', zero_mul, Real.deriv_exp, sub_zero, zero_add]
        ring
      rw [hderiv, deriv_fun_mul (by fun_prop) (by fun_prop),
        deriv_fun_mul (by fun_prop) (by fun_prop), _root_.deriv_exp (by fun_prop)]
      simp only [deriv_const', exp_zero, mul_one, deriv_id'', zero_add, sub_self, mul_zero]
      rw [_root_.deriv_exp (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop),
        deriv_fun_sub (by fun_prop) (by fun_prop)]
      simp only [exp_zero, sub_self, mul_zero, deriv_const', Real.deriv_exp, sub_zero,
        mul_one, zero_add, one_mul]
      ring

/-- The variance of a real-valued Poisson law is its rate. -/
@[simp]
theorem variance_id_map_cast_poissonMeasure (r : ℝ≥0) :
    variance id Po(ℝ, r) = r := by
  have hsq : Integrable (fun x : ℝ ↦ x ^ 2) Po(ℝ, r) :=
    integrable_pow_of_integrable_exp_mul (by norm_num : (1 : ℝ) ≠ 0)
      (integrable_exp_mul_id_map_cast_poissonMeasure r 1)
      (integrable_exp_mul_id_map_cast_poissonMeasure r (-1)) 2
  have hid : MemLp id 2 Po(ℝ, r) :=
    (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).2 (by simpa using hsq)
  rw [variance_eq_sub hid]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_map_cast_poissonMeasure,
    integral_id_map_cast_poissonMeasure]
  ring

/-- A real random variable with Poisson law has expectation equal to the rate. -/
theorem integral_of_hasLaw_map_cast_poissonMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {r : ℝ≥0} (hX : HasLaw X Po(ℝ, r) P) :
    ∫ ω, X ω ∂P = r := by
  rw [hX.integral_eq]
  exact integral_id_map_cast_poissonMeasure r

/-- A real random variable with Poisson law has variance equal to the rate. -/
theorem variance_of_hasLaw_map_cast_poissonMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {r : ℝ≥0} (hX : HasLaw X Po(ℝ, r) P) :
    variance X P = r := by
  rw [hX.variance_eq]
  exact variance_id_map_cast_poissonMeasure r

end TauCeti
