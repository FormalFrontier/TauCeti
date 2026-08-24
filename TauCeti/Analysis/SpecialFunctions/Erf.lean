/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The error function

This file defines the Gauss error function `erf x = (2 / √π) * ∫ t in 0..x, exp (-t ^ 2)` and its
complement `erfc x = 1 - erf x`, and develops their elementary real-variable theory: oddness,
strict monotonicity, the derivative, and the limits at both infinities.

These are the error-function targets of `TauCetiRoadmap/StandardDistributions/README.md`,
Layer 2.  The names and statement shapes follow those proposed for Mathlib in
[mathlib4#34053](https://github.com/leanprover-community/mathlib4/pull/34053), so that the
declarations here can be replaced by Mathlib's once it provides them.  The identification
`erf x = regularizedGamma (1 / 2) (x ^ 2)`, which holds for `0 ≤ x` — the right-hand side is even
in `x` while `erf` is odd — needs the incomplete gamma function and is not proved here.

The limits at infinity come from Mathlib's Gaussian integral `integral_gaussian_Ioi` together
with the improper-integral comparison `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`; the
derivative is the fundamental theorem of calculus for a continuous integrand.

## Main declarations

* `TauCeti.Real.erf` and `TauCeti.Real.erfc` — the error function and its complement.
* `TauCeti.Real.erf_neg` — the error function is odd.
* `TauCeti.Real.hasDerivAt_erf` — its derivative is `2 / √π * exp (-x ^ 2)`.
* `TauCeti.Real.strictMono_erf` — it is strictly monotone.
* `TauCeti.Real.tendsto_erf_atTop` and `TauCeti.Real.tendsto_erf_atBot` — its limits are `1` and
  `-1`, whence `TauCeti.Real.abs_erf_lt_one`.
-/

public section

noncomputable section

open MeasureTheory Filter Set Real
open scoped Topology

namespace TauCeti

namespace Real

/-- The Gauss error function, `erf x = (2 / √π) * ∫ t in 0..x, exp (-t ^ 2)`. -/
def erf (x : ℝ) : ℝ := 2 / √π * ∫ t in (0 : ℝ)..x, rexp (-t ^ 2)

/-- The complementary error function, `erfc x = 1 - erf x`. -/
def erfc (x : ℝ) : ℝ := 1 - erf x

/-- The defining integral formula for the error function. -/
theorem erf_def (x : ℝ) : erf x = 2 / √π * ∫ t in (0 : ℝ)..x, rexp (-t ^ 2) := (rfl)

/-- The defining formula for the complementary error function. -/
theorem erfc_def (x : ℝ) : erfc x = 1 - erf x := (rfl)

/-- The error function vanishes at the origin. -/
@[simp]
theorem erf_zero : erf 0 = 0 := by simp [erf_def]

/-- The complementary error function is `1` at the origin. -/
@[simp]
theorem erfc_zero : erfc 0 = 1 := by simp [erfc_def]

/-- The error function is odd. -/
@[simp]
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  have h : (∫ t in (0 : ℝ)..x, rexp (-t ^ 2)) = ∫ t in (-x)..(0 : ℝ), rexp (-t ^ 2) := by
    have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x)
      fun t : ℝ => rexp (-t ^ 2)
    simp only [neg_sq, neg_zero] at hcomp
    exact hcomp
  rw [erf_def, erf_def, h, intervalIntegral.integral_symm]
  ring

/-- The complementary error function reflects around the value `1`. -/
@[simp]
theorem erfc_neg (x : ℝ) : erfc (-x) = 2 - erfc x := by
  rw [erfc_def, erfc_def, erf_neg]; ring

/-- The error function is strictly differentiable, with derivative `2 / √π * exp (-x ^ 2)`. -/
theorem hasStrictDerivAt_erf (x : ℝ) : HasStrictDerivAt erf (2 / √π * rexp (-x ^ 2)) x :=
  ((by fun_prop : Continuous fun t : ℝ => rexp (-t ^ 2)).integral_hasStrictDerivAt 0 x).const_mul
    (2 / √π)

/-- The derivative of the error function. -/
theorem hasDerivAt_erf (x : ℝ) : HasDerivAt erf (2 / √π * rexp (-x ^ 2)) x :=
  (hasStrictDerivAt_erf x).hasDerivAt

/-- The derivative of the error function, in `deriv` form. -/
@[simp]
theorem deriv_erf : deriv erf = fun x => 2 / √π * rexp (-x ^ 2) :=
  funext fun x => (hasDerivAt_erf x).deriv

/-- The error function is differentiable. -/
theorem differentiable_erf : Differentiable ℝ erf := fun x => (hasDerivAt_erf x).differentiableAt

/-- The error function is continuous. -/
@[fun_prop]
theorem continuous_erf : Continuous erf := differentiable_erf.continuous

/-- The complementary error function is strictly differentiable, with derivative
`-(2 / √π * exp (-x ^ 2))`. -/
theorem hasStrictDerivAt_erfc (x : ℝ) :
    HasStrictDerivAt erfc (-(2 / √π * rexp (-x ^ 2))) x := by
  rw [funext erfc_def]
  exact (hasStrictDerivAt_erf x).const_sub 1

/-- The derivative of the complementary error function. -/
theorem hasDerivAt_erfc (x : ℝ) : HasDerivAt erfc (-(2 / √π * rexp (-x ^ 2))) x :=
  (hasStrictDerivAt_erfc x).hasDerivAt

/-- The derivative of the complementary error function, in `deriv` form. -/
@[simp]
theorem deriv_erfc : deriv erfc = fun x => -(2 / √π * rexp (-x ^ 2)) :=
  funext fun x => (hasDerivAt_erfc x).deriv

/-- The complementary error function is differentiable. -/
theorem differentiable_erfc : Differentiable ℝ erfc := fun x =>
  (hasDerivAt_erfc x).differentiableAt

/-- The complementary error function is continuous. -/
@[fun_prop]
theorem continuous_erfc : Continuous erfc := differentiable_erfc.continuous

/-- The error function is strictly increasing. -/
theorem strictMono_erf : StrictMono erf :=
  strictMono_of_hasDerivAt_pos hasDerivAt_erf fun x => by positivity

/-- The complementary error function is strictly decreasing. -/
theorem strictAnti_erfc : StrictAnti erfc := fun _ _ h => by
  simpa only [erfc_def, sub_lt_sub_iff_left] using strictMono_erf h

/-- The error function is positive on the positive half-line. -/
theorem erf_pos {x : ℝ} (hx : 0 < x) : 0 < erf x := by simpa using strictMono_erf hx

/-- The error function is nonnegative on the nonnegative half-line. -/
theorem erf_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ erf x := by simpa using strictMono_erf.monotone hx

/-- The Gaussian integral over the half-line, in the interval-integral form used by `erf`. -/
private theorem tendsto_intervalIntegral_exp_neg_sq_atTop :
    Tendsto (fun x : ℝ => ∫ t in (0 : ℝ)..x, rexp (-t ^ 2)) atTop (𝓝 (√π / 2)) := by
  have h := intervalIntegral_tendsto_integral_Ioi (μ := volume)
    (f := fun t : ℝ => rexp (-t ^ 2)) 0
      (by simpa using (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn) tendsto_id
  have hgauss : ∫ t in Ioi (0 : ℝ), rexp (-t ^ 2) = √π / 2 := by
    simpa using integral_gaussian_Ioi 1
  rwa [hgauss] at h

/-- The error function tends to `1` at `+∞`. -/
theorem tendsto_erf_atTop : Tendsto erf atTop (𝓝 1) := by
  have hπ : √π ≠ 0 := by positivity
  have h := tendsto_intervalIntegral_exp_neg_sq_atTop.const_mul (2 / √π)
  convert h.congr fun x => (erf_def x).symm using 2
  field_simp

/-- The error function tends to `-1` at `-∞`. -/
theorem tendsto_erf_atBot : Tendsto erf atBot (𝓝 (-1)) := by
  have h := (tendsto_erf_atTop.comp tendsto_neg_atBot_atTop).neg
  exact h.congr fun x => by simp [Function.comp_apply, erf_neg]

/-- The complementary error function tends to `0` at `+∞`. -/
theorem tendsto_erfc_atTop : Tendsto erfc atTop (𝓝 0) := by
  have h : Tendsto (fun x => 1 - erf x) atTop (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub tendsto_erf_atTop
  rw [sub_self] at h
  exact h.congr fun x => (erfc_def x).symm

/-- The complementary error function tends to `2` at `-∞`. -/
theorem tendsto_erfc_atBot : Tendsto erfc atBot (𝓝 2) := by
  have h : Tendsto (fun x => 1 - erf x) atBot (𝓝 (1 - -1)) :=
    tendsto_const_nhds.sub tendsto_erf_atBot
  norm_num at h
  exact h.congr fun x => (erfc_def x).symm

/-- The error function is bounded above by `1`. -/
theorem erf_le_one (x : ℝ) : erf x ≤ 1 :=
  ge_of_tendsto tendsto_erf_atTop <| eventually_atTop.2 ⟨x, fun _ hy => strictMono_erf.monotone hy⟩

/-- The error function never attains the value `1`. -/
theorem erf_lt_one (x : ℝ) : erf x < 1 :=
  (strictMono_erf (lt_add_one x)).trans_le (erf_le_one (x + 1))

/-- The error function never attains the value `-1`. -/
theorem neg_one_lt_erf (x : ℝ) : -1 < erf x := by
  have h := erf_lt_one (-x)
  rw [erf_neg] at h
  linarith

/-- The error function takes values in the open interval `(-1, 1)`. -/
theorem abs_erf_lt_one (x : ℝ) : |erf x| < 1 :=
  abs_lt.2 ⟨neg_one_lt_erf x, erf_lt_one x⟩

/-- The complementary error function is positive. -/
theorem erfc_pos (x : ℝ) : 0 < erfc x := by
  rw [erfc_def]; linarith [erf_lt_one x]

/-- The complementary error function is bounded above by `2`, strictly. -/
theorem erfc_lt_two (x : ℝ) : erfc x < 2 := by
  rw [erfc_def]; linarith [neg_one_lt_erf x]

end Real

end TauCeti
