/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Erf
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF

/-!
# The cumulative distribution function of a real Gaussian law

This file computes `ProbabilityTheory.cdf (gaussianReal m v)` in closed form.  For a nonzero
variance the answer is `(1 + erf ((x - m) / √(2 * v))) / 2`, and at the singular boundary
`v = 0` the law is a Dirac mass, with the step-function cdf.

These are the Gaussian entries of the closed-form cdf target of
`TauCetiRoadmap/StandardDistributions/README.md`, Layer 2.

The computation goes through the interval integral of `gaussianPDFReal`, which is an affine
change of variables away from the integral defining `TauCeti.Real.erf`; the improper integral
over `Set.Iic x` is then the limit of those interval integrals, using
`TauCeti.Real.tendsto_erf_atBot` for the contribution at `-∞`.

## Main declarations

* `TauCeti.intervalIntegral_gaussianPDFReal` — the Gaussian density integrates to a difference of
  error-function values.
* `TauCeti.integral_Iic_gaussianPDFReal` — the same over a left half-line.
* `TauCeti.cdf_gaussianReal_eq` — the closed-form cdf for a nonzero variance.
* `TauCeti.cdf_gaussianReal_zero_one` — the standard Gaussian cdf.
* `TauCeti.cdf_gaussianReal_zero` — the cdf at the singular boundary `v = 0`.
* `TauCeti.measureReal_Ioi_gaussianReal` — the upper tail, in terms of `TauCeti.Real.erfc`.
* `TauCeti.measureReal_le_of_hasLaw_gaussianReal` — the random-variable corollary.
-/

public section

noncomputable section

open MeasureTheory Filter Set Real ProbabilityTheory
open scoped Topology NNReal

namespace TauCeti

/-- On an interval, the Gaussian density integrates to the difference of two error-function
values. Both sides vanish at zero variance; otherwise the affine change of variables
`t ↦ (t - m) / √(2 * v)` turns the integral into the one defining `TauCeti.Real.erf`. -/
theorem intervalIntegral_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (a b : ℝ) :
    (∫ t in a..b, gaussianPDFReal m v t) =
      (Real.erf ((b - m) / √(2 * (v : ℝ))) - Real.erf ((a - m) / √(2 * (v : ℝ)))) / 2 := by
  by_cases hv : v = 0
  · subst v
    simp
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  set c : ℝ := √(2 * (v : ℝ)) with hcdef
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 2 * (v : ℝ) := Real.sq_sqrt (by positivity)
  -- Rewrite the density as a scalar multiple of the standard Gaussian kernel.
  have hdens : ∀ t : ℝ,
      gaussianPDFReal m v t = (√(2 * π * (v : ℝ)))⁻¹ * rexp (-((t - m) / c) ^ 2) := fun t => by
    rw [gaussianPDFReal, div_pow, hc2, neg_div]
  simp only [hdens]
  rw [intervalIntegral.integral_const_mul]
  -- Change variables.
  have h1 : (∫ t in a..b, rexp (-((t - m) / c) ^ 2)) =
      ∫ y in (a - m)..(b - m), rexp (-(y / c) ^ 2) :=
    intervalIntegral.integral_comp_sub_right (fun y : ℝ => rexp (-(y / c) ^ 2)) m
  have h2 : (∫ y in (a - m)..(b - m), rexp (-(y / c) ^ 2)) =
      c • ∫ s in ((a - m) / c)..((b - m) / c), rexp (-s ^ 2) :=
    intervalIntegral.integral_comp_div (f := fun s : ℝ => rexp (-s ^ 2)) hc.ne'
  have h3 : (∫ s in ((a - m) / c)..((b - m) / c), rexp (-s ^ 2)) =
      (∫ s in (0 : ℝ)..((b - m) / c), rexp (-s ^ 2)) -
        ∫ s in (0 : ℝ)..((a - m) / c), rexp (-s ^ 2) :=
    (intervalIntegral.integral_interval_sub_left
      ((by fun_prop : Continuous fun s : ℝ => rexp (-s ^ 2)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s : ℝ => rexp (-s ^ 2)).intervalIntegrable _ _)).symm
  have herf : ∀ z : ℝ, (∫ s in (0 : ℝ)..z, rexp (-s ^ 2)) = √π / 2 * Real.erf z := fun z => by
    rw [Real.erf_def]; field_simp
  -- The remaining constant is `1 / 2`.
  have hcs : c * √π = √(2 * π * (v : ℝ)) := by
    rw [hcdef, ← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  rw [h1, h2, h3, herf, herf, smul_eq_mul]
  rw [eq_div_iff (two_ne_zero), ← hcs]
  field_simp

/-- Over a left half-line, the Gaussian density integrates to
`(1 + erf ((x - m) / √(2 * v))) / 2`. -/
theorem integral_Iic_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    (∫ t in Iic x, gaussianPDFReal m v t) = (1 + Real.erf ((x - m) / √(2 * (v : ℝ)))) / 2 := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hc : 0 < √(2 * (v : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Iic (μ := volume)
    (f := gaussianPDFReal m v) x (integrable_gaussianPDFReal m v).integrableOn
    (a := id) tendsto_id
  have hy : Tendsto (fun y : ℝ => (y - m) / √(2 * (v : ℝ))) atBot atBot :=
    Tendsto.atBot_div_const hc <| by
      simpa [sub_eq_add_neg] using
        tendsto_atBot_add_const_right (f := fun y : ℝ => y) (l := atBot) (-m) tendsto_id
  have hlim' : Tendsto (fun y : ℝ => ∫ t in y..x, gaussianPDFReal m v t) atBot
      (𝓝 ((1 + Real.erf ((x - m) / √(2 * (v : ℝ)))) / 2)) := by
    have h := ((tendsto_const_nhds (x := Real.erf ((x - m) / √(2 * (v : ℝ)))) (f := atBot)).sub
      (Real.tendsto_erf_atBot.comp hy)).div_const 2
    convert h.congr fun y => (intervalIntegral_gaussianPDFReal m (v := v) y x).symm using 2
    ring
  exact tendsto_nhds_unique hlim hlim'

/-- The cumulative distribution function of a Gaussian law with nonzero variance. -/
theorem cdf_gaussianReal_eq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    cdf (gaussianReal m v) x = (1 + Real.erf ((x - m) / √(2 * (v : ℝ)))) / 2 := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral m hv,
    ENNReal.toReal_ofReal (integral_nonneg fun t => gaussianPDFReal_nonneg m v t)]
  exact integral_Iic_gaussianPDFReal m hv x

/-- The cumulative distribution function of the standard Gaussian law. -/
theorem cdf_gaussianReal_zero_one (x : ℝ) :
    cdf (gaussianReal 0 1) x = (1 + Real.erf (x / √2)) / 2 := by
  simpa using cdf_gaussianReal_eq 0 one_ne_zero x

/-- At the singular boundary `v = 0` the Gaussian law is a Dirac mass, and its cumulative
distribution function is the corresponding step function. -/
theorem cdf_gaussianReal_zero (m x : ℝ) :
    cdf (gaussianReal m 0) x = if m ≤ x then 1 else 0 := by
  rw [gaussianReal_zero_var, cdf_eq_real, measureReal_def, Measure.dirac_apply]
  by_cases h : m ≤ x <;> simp [h]

/-- The upper tail of a Gaussian law with nonzero variance is half the complementary error
function. -/
theorem measureReal_Ioi_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    (gaussianReal m v).real (Ioi x) = Real.erfc ((x - m) / √(2 * (v : ℝ))) / 2 := by
  have h : (gaussianReal m v).real (Iic x) = (1 + Real.erf ((x - m) / √(2 * (v : ℝ)))) / 2 := by
    rw [← cdf_eq_real]
    exact cdf_gaussianReal_eq m hv x
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, h, Real.erfc_def]
  simp only [probReal_univ]
  ring

/-- A random variable with a Gaussian law of nonzero variance has the error-function cumulative
distribution function. -/
theorem measureReal_le_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hX : HasLaw X (gaussianReal m v) P) (x : ℝ) :
    P.real {ω | X ω ≤ x} = (1 + Real.erf ((x - m) / √(2 * (v : ℝ)))) / 2 := by
  rw [hX.measureReal_eq (p := fun y : ℝ => y ≤ x) measurableSet_Iic, Set.Iic_def, ← cdf_eq_real]
  exact cdf_gaussianReal_eq m hv x

end TauCeti
