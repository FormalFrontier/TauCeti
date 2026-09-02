/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.Distributions.PDFInstances

/-!
# Elementary theory of the Pareto distribution

This file completes the elementary API for Mathlib's Pareto measure.  For positive threshold
`t` and shape `r`, it proves the exact real-power moment criterion and formula, then derives the
mean, variance, and the matching non-integrability statements at the sharp thresholds.  It also
computes the cdf and the exact domain of exponential integrability.

The common calculation is

`∫ x, x ^ q ∂paretoMeasure t r = r * t ^ q / (r - q)` for `q < r`.

Here `^` on a real exponent is `Real.rpow`.  The density is supported on `[t, ∞)`, where all
bases are positive, so Mathlib's improper-integral criterion for real powers applies directly.

## Main results

* `ProbabilityTheory.integrable_rpow_paretoMeasure_iff` and
  `ProbabilityTheory.integral_rpow_paretoMeasure` give the sharp moment criterion and value.
* `ProbabilityTheory.integral_id_paretoMeasure` and
  `ProbabilityTheory.variance_id_paretoMeasure` compute the mean and variance.
* `ProbabilityTheory.cdf_paretoMeasure_eq` computes the cdf.
* `ProbabilityTheory.integrableExpSet_id_paretoMeasure` identifies the exponential-moment
  domain as `Set.Iic 0`.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, the Pareto target — the
  mean and its non-integrability threshold, the variance and its non-integrability threshold,
  the cdf, and `integrableExpSet id (paretoMeasure t r) = Set.Iic 0`.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  Chapter 20.
* `Mathlib.Probability.Distributions.Pareto`, whose density normalization is reused here.
-/

public section

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal Interval

namespace ProbabilityTheory

variable {t r q : ℝ}

private theorem paretoPDF_toReal (ht : 0 < t) (hr : 0 < r) (x : ℝ) :
    (paretoPDF t r x).toReal =
      if t ≤ x then r * t ^ r * x ^ (-(r + 1)) else 0 := by
  rw [paretoPDF_eq, ENNReal.toReal_ofReal]
  split_ifs with hx
  · simpa [paretoPDFReal, hx] using paretoPDFReal_nonneg ht.le hr.le x
  · exact le_rfl

/-- The Pareto density times `x ^ q` is, on the support, the constant `r * t ^ r` times the
single real power `x ^ (q - r - 1)`, and vanishes off the support. -/
private theorem paretoPDF_toReal_mul_rpow (ht : 0 < t) (hr : 0 < r) (q x : ℝ) :
    (paretoPDF t r x).toReal * x ^ q =
      Set.indicator (Set.Ici t) (fun y => r * t ^ r * y ^ (q - r - 1)) x := by
  rw [paretoPDF_toReal ht hr]
  by_cases hx : t ≤ x
  · have hx0 : 0 < x := ht.trans_le hx
    have hexponent : -(r + 1) + q = q - r - 1 := by ring
    simp only [Set.indicator_apply, Set.mem_Ici, hx, ite_true]
    rw [mul_assoc, ← Real.rpow_add hx0, hexponent]
  · simp [hx]

private theorem paretoPDF_lt_top (t r : ℝ) :
    (∀ᵐ x : ℝ ∂volume, paretoPDF t r x < ∞) := by
  filter_upwards with x
  rw [paretoPDF_eq]
  exact ENNReal.ofReal_lt_top

private theorem ae_paretoMeasure_mem_Ici (t r : ℝ) :
    ∀ᵐ x : ℝ ∂paretoMeasure t r, t ≤ x := by
  rw [paretoMeasure, ae_withDensity_iff (TauCeti.Probability.measurable_paretoPDF t r)]
  filter_upwards with x
  intro hpdf
  by_contra htx
  apply hpdf
  exact paretoPDF_of_lt (lt_of_not_ge htx)

/-- A real power is integrable under a nondegenerate Pareto law exactly below the shape
parameter. -/
@[simp]
theorem integrable_rpow_paretoMeasure_iff (ht : 0 < t) (hr : 0 < r) (q : ℝ) :
    Integrable (fun x : ℝ => x ^ q) (paretoMeasure t r) ↔ q < r := by
  rw [paretoMeasure, integrable_withDensity_iff (TauCeti.Probability.measurable_paretoPDF t r)
    (paretoPDF_lt_top t r)]
  have hfun : (fun x : ℝ => x ^ q * (paretoPDF t r x).toReal) =
      Set.indicator (Set.Ici t) (fun y => r * t ^ r * y ^ (q - r - 1)) := by
    funext x
    rw [mul_comm]
    exact paretoPDF_toReal_mul_rpow ht hr q x
  rw [hfun, integrable_indicator_iff measurableSet_Ici]
  rw [integrableOn_congr_set_ae Ioi_ae_eq_Ici.symm]
  have hc : IsUnit (r * t ^ r) := isUnit_iff_ne_zero.mpr <|
    mul_ne_zero hr.ne' (Real.rpow_pos_of_pos ht _).ne'
  have hconst :
      IntegrableOn (fun x : ℝ => (r * t ^ r) * x ^ (q - r - 1)) (Ioi t) ↔
        IntegrableOn (fun x : ℝ => x ^ (q - r - 1)) (Ioi t) := by
    simpa only [IntegrableOn] using
      (integrable_const_mul_iff (μ := volume.restrict (Ioi t)) hc
        (fun x : ℝ => x ^ (q - r - 1)))
  rw [hconst, integrableOn_Ioi_rpow_iff ht]
  constructor <;> intro h <;> linarith

/-- The `q`-th real-power moment of a Pareto law is `r * t ^ q / (r - q)` below the
shape parameter. -/
theorem integral_rpow_paretoMeasure (ht : 0 < t) (hr : 0 < r) (hq : q < r) :
    ∫ x : ℝ, x ^ q ∂paretoMeasure t r = r * t ^ q / (r - q) := by
  rw [paretoMeasure, integral_withDensity_eq_integral_toReal_smul
    (TauCeti.Probability.measurable_paretoPDF t r) (paretoPDF_lt_top t r)]
  simp only [smul_eq_mul]
  have hfun : (fun x : ℝ => (paretoPDF t r x).toReal * x ^ q) =
      Set.indicator (Set.Ici t) (fun y => r * t ^ r * y ^ (q - r - 1)) :=
    funext fun x => paretoPDF_toReal_mul_rpow ht hr q x
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ht]
  have hexponent : q - r - 1 + 1 = q - r := by ring
  rw [hexponent]
  have hpow : t ^ r * t ^ (q - r) = t ^ q := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [← hpow]
  have hqr_ne : q - r ≠ 0 := by linarith
  have hrq_ne : r - q ≠ 0 := by linarith
  field_simp [hqr_ne, hrq_ne]
  ring

/-- The mean of a Pareto law is `r * t / (r - 1)` when `1 < r`. -/
theorem integral_id_paretoMeasure (ht : 0 < t) (hr : 1 < r) :
    ∫ x : ℝ, x ∂paretoMeasure t r = r * t / (r - 1) := by
  simpa [Real.rpow_one] using integral_rpow_paretoMeasure ht (by linarith) hr

/-- The identity is integrable under a Pareto law exactly when the shape exceeds `1`. -/
@[simp]
theorem integrable_id_paretoMeasure_iff (ht : 0 < t) (hr : 0 < r) :
    Integrable id (paretoMeasure t r) ↔ 1 < r := by
  have hid_rpow : (id : ℝ → ℝ) = fun x => x ^ (1 : ℝ) := by
    funext x
    simp only [id_eq, Real.rpow_one]
  rw [hid_rpow, integrable_rpow_paretoMeasure_iff ht hr]

/-- At or below shape `1`, a nondegenerate Pareto law has no finite mean. -/
theorem not_integrable_id_paretoMeasure (ht : 0 < t) (hr : 0 < r) (h : r ≤ 1) :
    ¬ Integrable id (paretoMeasure t r) := by
  rw [integrable_id_paretoMeasure_iff ht hr]
  exact not_lt.mpr h

/-- The second raw moment of a Pareto law is `r * t² / (r - 2)` when `2 < r`. -/
theorem integral_sq_paretoMeasure (ht : 0 < t) (hr : 2 < r) :
    ∫ x : ℝ, x ^ 2 ∂paretoMeasure t r = r * t ^ 2 / (r - 2) := by
  have h := integral_rpow_paretoMeasure (q := (2 : ℝ)) ht (by linarith) hr
  simpa [Real.rpow_two] using h

/-- Squaring is integrable under a Pareto law exactly when the shape exceeds `2`. -/
@[simp]
theorem integrable_sq_paretoMeasure_iff (ht : 0 < t) (hr : 0 < r) :
    Integrable (fun x : ℝ => x ^ 2) (paretoMeasure t r) ↔ 2 < r := by
  simpa [Real.rpow_two] using integrable_rpow_paretoMeasure_iff ht hr 2

/-- At or below shape `2`, the second raw moment of a nondegenerate Pareto law diverges. -/
theorem not_integrable_sq_paretoMeasure (ht : 0 < t) (hr : 0 < r) (h : r ≤ 2) :
    ¬ Integrable (fun x : ℝ => x ^ 2) (paretoMeasure t r) := by
  rw [integrable_sq_paretoMeasure_iff ht hr]
  exact not_lt.mpr h

/-- The variance of a Pareto law is `r * t² / ((r - 1)² * (r - 2))` when `2 < r`. -/
theorem variance_id_paretoMeasure (ht : 0 < t) (hr : 2 < r) :
    variance id (paretoMeasure t r) = r * t ^ 2 / ((r - 1) ^ 2 * (r - 2)) := by
  let _ : IsProbabilityMeasure (paretoMeasure t r) :=
    isProbabilityMeasure_paretoMeasure ht (by linarith)
  have hmem : MemLp id 2 (paretoMeasure t r) := by
    rw [memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable]
    simpa [id_eq] using (integrable_sq_paretoMeasure_iff ht (by linarith)).mpr hr
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_id_paretoMeasure ht (by linarith), integral_sq_paretoMeasure ht hr]
  have hr1_ne : r - 1 ≠ 0 := by linarith
  have hr2_ne : r - 2 ≠ 0 := by linarith
  field_simp [hr1_ne, hr2_ne]
  ring

/-- The cdf of a nondegenerate Pareto law: it vanishes below the threshold and equals
`1 - (t / x) ^ r` on and above it. -/
@[simp]
theorem cdf_paretoMeasure_eq (ht : 0 < t) (hr : 0 < r) (x : ℝ) :
    cdf (paretoMeasure t r) x = if x < t then 0 else 1 - (t / x) ^ r := by
  rw [cdf_paretoMeasure_eq_integral ht hr]
  by_cases hx : x < t
  · rw [ite_eq_left hx]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    rw [paretoPDFReal]
    simp [not_le.mpr (hy.trans_lt hx)]
  · rw [ite_eq_right hx]
    have htx : t ≤ x := not_lt.mp hx
    have hx0 : 0 < x := ht.trans_le htx
    have hrestrict : (∫ y in Set.Iic x, paretoPDFReal t r y) =
        ∫ y in Set.Ioc t x, paretoPDFReal t r y := by
      apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Iic.nullMeasurableSet
        (Set.Ioc_subset_Iic_self.trans (Set.Iic_subset_Iic.mpr le_rfl))
      filter_upwards [volume.ae_ne t] with y hyt hy
      rw [paretoPDFReal]
      have hnot : ¬ t ≤ y := fun hty =>
        hy.2 ⟨lt_of_le_of_ne hty (Ne.symm hyt), hy.1⟩
      simp [hnot]
    rw [hrestrict, ← intervalIntegral.integral_of_le htx]
    have heq : (∫ y in t..x, paretoPDFReal t r y) =
        ∫ y in t..x, (r * t ^ r) * y ^ (-(r + 1)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le htx] at hy
      simp [paretoPDFReal, hy.1]
    rw [heq]
    have hzero : (0 : ℝ) ∉ Set.uIcc t x := by
      rw [uIcc_of_le htx]
      exact fun h => (ht.trans_le h.1).ne' rfl
    rw [intervalIntegral.integral_const_mul, integral_rpow
      (Or.inr ⟨by linarith, hzero⟩)]
    have hexponent : -(r + 1) + 1 = -r := by ring
    rw [hexponent, Real.rpow_neg ht.le,
      Real.rpow_neg hx0.le, Real.div_rpow ht.le hx0.le]
    field_simp [hr.ne', (Real.rpow_pos_of_pos ht r).ne', (Real.rpow_pos_of_pos hx0 r).ne']
    ring

/-- Every nonpositive exponential rate is integrable under a nondegenerate Pareto law. -/
theorem integrable_exp_mul_id_paretoMeasure_of_nonpos (ht : 0 < t) (hr : 0 < r)
    {u : ℝ} (hu : u ≤ 0) :
    Integrable (fun x : ℝ => Real.exp (u * x)) (paretoMeasure t r) := by
  let _ : IsProbabilityMeasure (paretoMeasure t r) :=
    isProbabilityMeasure_paretoMeasure ht hr
  apply Integrable.of_bound (by fun_prop) (Real.exp (u * t))
  filter_upwards [ae_paretoMeasure_mem_Ici t r] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx hu)

/-- The exponential of a multiple of the identity is integrable under a nondegenerate Pareto
law exactly when the rate is nonpositive. -/
@[simp]
theorem integrable_exp_mul_id_paretoMeasure_iff (ht : 0 < t) (hr : 0 < r) (u : ℝ) :
    Integrable (fun x : ℝ => Real.exp (u * x)) (paretoMeasure t r) ↔ u ≤ 0 := by
  refine ⟨fun h => ?_, integrable_exp_mul_id_paretoMeasure_of_nonpos ht hr⟩
  by_contra hu
  have hu_pos : 0 < u := lt_of_not_ge hu
  have hneg : Integrable (fun x : ℝ => Real.exp (-u * x)) (paretoMeasure t r) :=
    integrable_exp_mul_id_paretoMeasure_of_nonpos ht hr (neg_nonpos.mpr hu_pos.le)
  have hmoment : Integrable (fun x : ℝ => x ^ r) (paretoMeasure t r) :=
    integrable_rpow_of_integrable_exp_mul hu_pos.ne' h hneg hr.le
  exact (lt_irrefl r) ((integrable_rpow_paretoMeasure_iff ht hr r).mp hmoment)

/-- The exact exponential-integrability domain of the identity under a nondegenerate Pareto law
is the nonpositive half-line. -/
@[simp]
theorem integrableExpSet_id_paretoMeasure (ht : 0 < t) (hr : 0 < r) :
    integrableExpSet id (paretoMeasure t r) = Set.Iic 0 := by
  ext u
  simpa [integrableExpSet, id_eq] using integrable_exp_mul_id_paretoMeasure_iff ht hr u

end ProbabilityTheory

end

end
