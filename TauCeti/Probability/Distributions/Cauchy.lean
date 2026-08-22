/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance

/-!
# The cumulative distribution function of the Cauchy distribution

This file computes the cumulative distribution function of Mathlib's Cauchy law. For nonzero
scale `γ`, its value at `x` is

`1 / 2 + arctan ((x - x₀) / γ) / π`.

At scale zero Mathlib defines `cauchyMeasure x₀ 0` to be the Dirac mass at `x₀`. The file records
the corresponding cumulative distribution function, mean, variance, exponential-integrability
domain, moment-generating function, and cumulant-generating function. Keeping the singular case
separate prevents the density calculation for positive scale from being applied where the law is
not absolutely continuous.

## Main results

* `TauCeti.cdf_cauchyMeasure_eq` — the Cauchy cdf at nonzero scale;
* `TauCeti.cdf_cauchyMeasure_zero_scale` — the cdf of the zero-scale Dirac law;
* `TauCeti.integral_id_cauchyMeasure_zero_scale` and
  `TauCeti.variance_id_cauchyMeasure_zero_scale` — its mean and variance;
* `TauCeti.integrableExpSet_id_cauchyMeasure_zero_scale`,
  `TauCeti.mgf_id_cauchyMeasure_zero_scale`, and
  `TauCeti.cgf_id_cauchyMeasure_zero_scale` — its exponential moments.

## References

* Tau Ceti roadmap, `StandardDistributions`, Layer 1, "Cauchy".
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994.
-/

public section

namespace TauCeti

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

/-- The Cauchy density has the expected antiderivative on a left half-line. This is the analytic
calculation behind `cdf_cauchyMeasure_eq`. -/
private theorem integral_Iic_cauchyPDFReal (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) :
    ∫ y in Iic x, cauchyPDFReal x₀ γ y =
      1 / 2 + Real.arctan ((x - x₀) / (γ : ℝ)) / Real.pi := by
  have hγr : (γ : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hγ
  let F : ℝ → ℝ := fun y => Real.pi⁻¹ * Real.arctan ((y - x₀) / (γ : ℝ))
  have hderiv (y : ℝ) : HasDerivAt F (cauchyPDFReal x₀ γ y) y := by
    have hinner : HasDerivAt (fun z : ℝ => (z - x₀) / (γ : ℝ)) (γ : ℝ)⁻¹ y := by
      simpa only [one_div] using ((hasDerivAt_id' y).sub_const x₀).div_const (γ : ℝ)
    have h := ((Real.hasDerivAt_arctan ((y - x₀) / (γ : ℝ))).comp y hinner).const_mul
      Real.pi⁻¹
    have hvalue :
        Real.pi⁻¹ * ((1 / (1 + ((y - x₀) / (γ : ℝ)) ^ 2)) * (γ : ℝ)⁻¹) =
          cauchyPDFReal x₀ γ y := by
      rw [cauchyPDFReal_def']
      field_simp [hγr]
      simp [hγr]
    simpa only [F, Function.comp_apply, hvalue] using h
  have hint : IntegrableOn (cauchyPDFReal x₀ γ) (Iic x) :=
    (integrable_cauchyPDFReal (γ := γ) x₀).integrableOn
  have hsub_bot : Tendsto (fun y : ℝ => y - x₀) atBot atBot := by
    simpa [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-x₀) tendsto_id
  have hinner_bot : Tendsto (fun y : ℝ => (y - x₀) / (γ : ℝ)) atBot atBot :=
    hsub_bot.atBot_div_const (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ))
  have hF_bot : Tendsto F atBot (nhds (Real.pi⁻¹ * (-(Real.pi / 2)))) := by
    have harctan : Tendsto (fun y : ℝ => Real.arctan ((y - x₀) / (γ : ℝ))) atBot
        (nhds (-(Real.pi / 2))) :=
      (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp hinner_bot
    simpa only [F] using harctan.const_mul Real.pi⁻¹
  rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun y _ => hderiv y) hint hF_bot]
  dsimp only [F]
  field_simp [Real.pi_ne_zero]
  ring

/-- **The cumulative distribution function of a nondegenerate Cauchy law.** -/
@[simp]
theorem cdf_cauchyMeasure_eq (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) (x : ℝ) :
    cdf (cauchyMeasure x₀ γ) x =
      1 / 2 + Real.arctan ((x - x₀) / (γ : ℝ)) / Real.pi := by
  rw [cdf_eq_real, cauchyMeasure_of_scale_ne_zero x₀ hγ, Measure.real,
    withDensity_apply _ measurableSet_Iic]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Iic x)] cauchyPDFReal x₀ γ :=
    ae_of_all _ fun y => (cauchyPDF_pos x₀ hγ y).le
  simp_rw [cauchyPDF_def]
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg
    (measurable_cauchyPDFReal x₀ γ).aestronglyMeasurable]
  exact integral_Iic_cauchyPDFReal x₀ hγ x

/-- **The cumulative distribution function at zero scale.** Mathlib totalizes the Cauchy family
by setting `cauchyMeasure x₀ 0 = Measure.dirac x₀`. -/
theorem cdf_cauchyMeasure_zero_scale (x₀ x : ℝ) :
    cdf (cauchyMeasure x₀ 0) x = if x₀ ≤ x then 1 else 0 := by
  rw [cauchyMeasure_zero_scale, cdf_eq_real, Measure.real]
  by_cases h : x₀ ≤ x <;> simp [Measure.dirac_apply' _ measurableSet_Iic, h]

/-- The mean of the zero-scale Cauchy law is its location. -/
theorem integral_id_cauchyMeasure_zero_scale (x₀ : ℝ) :
    ∫ x, x ∂cauchyMeasure x₀ 0 = x₀ := by
  rw [cauchyMeasure_zero_scale, integral_dirac]

/-- The zero-scale Cauchy law has zero variance. -/
theorem variance_id_cauchyMeasure_zero_scale (x₀ : ℝ) :
    variance id (cauchyMeasure x₀ 0) = 0 := by
  rw [cauchyMeasure_zero_scale, variance_dirac]

/-- Every exponential moment of the zero-scale Cauchy law exists. -/
theorem integrableExpSet_id_cauchyMeasure_zero_scale (x₀ : ℝ) :
    integrableExpSet id (cauchyMeasure x₀ 0) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, cauchyMeasure_zero_scale, Set.mem_univ,
    iff_true]
  exact integrable_dirac (by simp)

/-- The moment-generating function of the zero-scale Cauchy law. -/
theorem mgf_id_cauchyMeasure_zero_scale (x₀ t : ℝ) :
    mgf id (cauchyMeasure x₀ 0) t = Real.exp (t * x₀) := by
  simpa using (mgf_dirac' (X := id) (ω := x₀) (t := t))

/-- The cumulant-generating function of the zero-scale Cauchy law. -/
theorem cgf_id_cauchyMeasure_zero_scale (x₀ t : ℝ) :
    cgf id (cauchyMeasure x₀ 0) t = t * x₀ := by
  rw [cgf, mgf_id_cauchyMeasure_zero_scale, Real.log_exp]

end TauCeti
