/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Moments of the real Gaussian distribution

This file computes the centered moments of Mathlib's real Gaussian measure.  The absolute
centered moment is evaluated first from the Gaussian density and Euler's Gamma integral; the
ordinary even and odd centered moments then follow from this formula and symmetry.

The formulas follow the real-Gaussian entry in the StandardDistributions roadmap and the standard
calculation in, for example, Johnson, Kotz, and Balakrishnan, *Continuous Univariate
Distributions*, volume 1, Chapter 13.

## Main results

* `integral_abs_sub_pow_gaussianReal` evaluates every absolute centered moment.
* `centralMoment_id_two_mul_gaussianReal` evaluates the even centered moments.
* `centralMoment_id_two_mul_add_one_gaussianReal` says that every odd centered moment vanishes.
-/

public section

open scoped Nat NNReal Real

namespace TauCeti

open MeasureTheory ProbabilityTheory Real Set

private lemma integral_abs_pow_mul_exp_neg_mul_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, |x| ^ n * exp (-b * x ^ 2) =
      b ^ (-((n : ℝ) + 1) / 2) * Gamma (((n : ℝ) + 1) / 2) := by
  calc
    _ = ∫ x : ℝ, (fun y : ℝ ↦ y ^ (n : ℝ) * exp (-b * y ^ 2)) |x| := by
      congr with x
      simp only [Real.rpow_natCast, sq_abs]
    _ = 2 * ∫ x : ℝ in Ioi 0, x ^ (n : ℝ) * exp (-b * x ^ 2) :=
      integral_comp_abs (f := fun y : ℝ ↦ y ^ (n : ℝ) * exp (-b * y ^ 2))
    _ = _ := by
      have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ)) (b := b)
        (hp := two_pos) (hq := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) (hb := hb)
      have h' : ∫ x : ℝ in Ioi 0, x ^ (n : ℝ) * exp (-b * x ^ 2) =
          b ^ (-((n : ℝ) + 1) / 2) * (1 / 2) * Gamma (((n : ℝ) + 1) / 2) := by
        rw [← h]
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
        rw [Real.rpow_two]
      calc
        _ = 2 * (b ^ (-((n : ℝ) + 1) / 2) * (1 / 2) *
            Gamma (((n : ℝ) + 1) / 2)) := congrArg (2 * ·) h'
        _ = _ := by ring

private lemma gaussian_absolute_moment_algebra (n : ℕ) {v : ℝ} (hv : 0 < v) :
    (√(2 * π * v))⁻¹ *
        ((2 * v)⁻¹ ^ (-((n : ℝ) + 1) / 2) * Gamma (((n : ℝ) + 1) / 2)) =
      (2 * v) ^ ((n : ℝ) / 2) * Gamma (((n : ℝ) + 1) / 2) / √π := by
  have hv₂ : 0 < 2 * v := mul_pos two_pos hv
  have hradicand : 2 * π * v = π * (2 * v) := by ring
  have hneg : -((n : ℝ) + 1) / 2 = -(((n : ℝ) + 1) / 2) := by ring
  have hsplit : ((n : ℝ) + 1) / 2 = (n : ℝ) / 2 + 1 / 2 := by ring
  rw [hradicand, Real.sqrt_mul pi_pos.le,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    hneg,
    Real.inv_rpow hv₂.le, Real.rpow_neg hv₂.le, inv_inv]
  rw [hsplit, Real.rpow_add hv₂]
  field_simp [Real.sqrt_ne_zero'.mpr pi_pos, (Real.rpow_pos_of_pos hv₂ _).ne']

/-- The `n`th absolute centered moment of a real Gaussian distribution. -/
@[simp]
theorem integral_abs_sub_pow_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    ∫ x, |x - m| ^ n ∂gaussianReal m v =
      (2 * (v : ℝ)) ^ ((n : ℝ) / 2) * Gamma (((n : ℝ) + 1) / 2) / √π := by
  by_cases hv : v = 0
  · subst v
    cases n with
    | zero =>
        simp only [gaussianReal_zero_var, MeasureTheory.integral_dirac, pow_zero, Nat.cast_zero,
          zero_div, Real.rpow_zero, zero_add]
        rw [one_mul, Real.Gamma_one_half_eq]
        field_simp [Real.sqrt_ne_zero'.mpr pi_pos]
    | succ n =>
        simp only [gaussianReal_zero_var, MeasureTheory.integral_dirac, sub_self, abs_zero,
          zero_pow (Nat.succ_ne_zero n), NNReal.coe_zero, Nat.cast_add, Nat.cast_one]
        simp only [mul_zero]
        rw [Real.zero_rpow (by positivity : ((n : ℝ) + 1) / 2 ≠ 0)]
        simp
  have hv' : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  calc
    _ = ∫ x, |x| ^ n ∂(gaussianReal m v).map (fun x ↦ x - m) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ x, |x| ^ n ∂gaussianReal 0 v := by simp [gaussianReal_map_sub_const]
    _ = ∫ x, gaussianPDFReal 0 v x * |x| ^ n :=
      integral_gaussianReal_eq_integral_smul hv
    _ = (√(2 * π * (v : ℝ)))⁻¹ *
        ∫ x : ℝ, |x| ^ n * exp (-(2 * (v : ℝ))⁻¹ * x ^ 2) := by
      rw [← integral_const_mul]
      congr with x
      rw [gaussianPDFReal]
      simp only [sub_zero]
      have hexponent : -(x ^ 2) / (2 * (v : ℝ)) = -(2 * (v : ℝ))⁻¹ * x ^ 2 := by
        field_simp
      rw [hexponent]
      ring
    _ = (√(2 * π * (v : ℝ)))⁻¹ *
        ((2 * (v : ℝ))⁻¹ ^ (-((n : ℝ) + 1) / 2) * Gamma (((n : ℝ) + 1) / 2)) := by
      rw [integral_abs_pow_mul_exp_neg_mul_sq n (inv_pos.mpr (mul_pos two_pos hv'))]
    _ = _ := gaussian_absolute_moment_algebra n hv'

/-- The `2n`th centered moment of a real Gaussian distribution is
`vⁿ (2n - 1)‼`. -/
@[simp]
theorem centralMoment_id_two_mul_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (gaussianReal m v) =
      (v : ℝ) ^ n * (2 * n - 1 : ℕ)‼ := by
  simp only [centralMoment, Pi.sub_apply, Pi.pow_apply, id_eq]
  rw [integral_id_gaussianReal]
  have heven_abs : (∫ x, (x - m) ^ (2 * n) ∂gaussianReal m v) =
      ∫ x, |x - m| ^ (2 * n) ∂gaussianReal m v := by
    congr with x
    simp only [pow_mul, sq_abs]
  rw [heven_abs]
  rw [integral_abs_sub_pow_gaussianReal]
  have hhalf_even : ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) := by norm_num
  have hhalf_succ : (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 := by
    push_cast
    ring
  rw [hhalf_even, Real.rpow_natCast, hhalf_succ, Real.Gamma_nat_add_half]
  field_simp [Real.sqrt_ne_zero'.mpr pi_pos]
  simp only [mul_pow]

/-- Every odd centered moment of a real Gaussian distribution vanishes. -/
@[simp]
theorem centralMoment_id_two_mul_add_one_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n + 1) (gaussianReal m v) = 0 := by
  simp only [centralMoment, Pi.sub_apply, Pi.pow_apply, id_eq]
  rw [integral_id_gaussianReal]
  have hmap : (gaussianReal m v).map (fun x ↦ x - m) = gaussianReal 0 v := by
    simpa using gaussianReal_map_sub_const (μ := m) (v := v) m
  have hcentered_map : (∫ x, (x - m) ^ (2 * n + 1) ∂gaussianReal m v) =
      ∫ x, x ^ (2 * n + 1) ∂(gaussianReal m v).map (fun x ↦ x - m) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  rw [hcentered_map]
  rw [hmap]
  have hsym : (gaussianReal 0 v).map (fun x : ℝ ↦ -x) = gaussianReal 0 v := by
    simpa using gaussianReal_map_neg (μ := 0) (v := v)
  have hneg : (∫ x, x ^ (2 * n + 1) ∂gaussianReal 0 v) =
      -(∫ x, x ^ (2 * n + 1) ∂gaussianReal 0 v) := by
    calc
      _ = ∫ x, x ^ (2 * n + 1) ∂(gaussianReal 0 v).map (fun x : ℝ ↦ -x) := by
        rw [hsym]
      _ = ∫ x, (-x) ^ (2 * n + 1) ∂gaussianReal 0 v := by
        rw [integral_map (by fun_prop) (by fun_prop)]
      _ = ∫ x, -(x ^ (2 * n + 1)) ∂gaussianReal 0 v := by
        congr with x
        exact (odd_two_mul_add_one n).neg_pow x
      _ = _ := integral_neg _
  linarith

end TauCeti
