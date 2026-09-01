/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Dirac
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import TauCeti.Probability.Distributions.Measurability
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The log-normal distribution

The log-normal law with log-mean `m` and log-variance `v` is the law of `exp X` for a Gaussian
`X`, so it is *defined* here as the pushforward `(gaussianReal m v).map Real.exp` and its density
is derived, not assumed.

This file proves the elementary theory of that law: it is a probability measure, it is carried by
the positive half-line, its density against Lebesgue measure is
`(x * √(2 * π * v))⁻¹ * exp (-(log x - m) ^ 2 / (2 * v))` for `v ≠ 0`, its cdf is the
error-function formula in `log x`, all of its raw moments are `exp (n * m + n ^ 2 * v / 2)`, its
exponential moments exist exactly for nonpositive `t`, and the family is measurable in its
parameters.

**Boundary.** At `v = 0` the Gaussian is a Dirac mass, so `logNormalMeasure m 0` is the Dirac mass
at `exp m` (`logNormalMeasure_zero_var`). That law is singular with respect to Lebesgue measure,
which is why the density and cdf theorems carry `v ≠ 0`, and its exponential-integrability domain
is all of `ℝ` rather than `Set.Iic 0`; the boundary cdf, mgf, cgf and characteristic function are
recorded separately. The moment formula, and hence the mean and the variance, need no hypothesis
on `v` at all.

## Main definitions

* `TauCeti.Probability.logNormalMeasure` — the law, as `(gaussianReal m v).map Real.exp`;
* `TauCeti.Probability.logNormalPDFReal` and `TauCeti.Probability.logNormalPDF` — its density
  against Lebesgue measure, in real- and `ℝ≥0∞`-valued form.

## Main results

* `logNormalMeasure_eq_withDensity`, `hasPDF_of_hasLaw_logNormalMeasure` and
  `rnDeriv_logNormalMeasure` — the density, the `HasPDF` bridge and the Radon–Nikodym derivative;
* `cdf_logNormalMeasure_eq` and `cdf_logNormalMeasure_zero_var` — the cdf and its boundary form;
* `integral_pow_logNormalMeasure`, `integral_id_logNormalMeasure` and
  `variance_id_logNormalMeasure` — the raw moments `exp (n * m + n ^ 2 * v / 2)`, the mean
  `exp (m + v / 2)` and the variance `(exp v - 1) * exp (2 * m + v)`;
* `integrableExpSet_id_logNormalMeasure` — the exponential moments exist exactly for `t ≤ 0`, with
  `not_integrable_exp_mul_logNormalMeasure` the matching non-integrability for `t > 0`;
* `mgf_id_logNormalMeasure_zero_var`, `cgf_id_logNormalMeasure_zero_var` and
  `charFun_logNormalMeasure_zero_var` — the boundary transforms;
* `measurable_logNormalMeasure` — the family is measurable in its parameters, so it can be used as
  a kernel.

## Implementation

Everything except the density and the failure of the exponential moments is read off the Gaussian
law through the pushforward. The moments are the Gaussian moment-generating function evaluated at
natural numbers, the cdf is the Gaussian cdf at `log x` because `exp ⁻¹' Iic x = Iic (log x)` for
`0 < x`, and the boundary law is `Measure.map_dirac`.

The density is the one genuine change of variables. Since `Real.exp` is injective with derivative
`exp` and image `Set.Ioi 0`, Mathlib's one-dimensional Jacobian formula
`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul` turns the mass that the pushforward
assigns to a measurable set `s` — an integral of the Gaussian density over `exp ⁻¹' s` — into an
integral of `logNormalPDF` over `s ∩ Set.Ioi 0`, and `logNormalPDF` vanishes off `Set.Ioi 0`.

The failure of the exponential moments for `t > 0` is a growth statement:
`t * exp x - (x - m) ^ 2 / (2 * v)` tends to `atTop`, so the integrand of the moment-generating
function, pulled back along `exp`, is eventually at least `1` on a half-line of infinite Lebesgue
measure.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, the **Log-normal** target,
  together with the log-normal case of the items 1–4 required of every family in "What every
  distribution must provide".
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1, 2nd ed.,
  Wiley (1994), ch. 14.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal NNReal Topology

namespace TauCeti

namespace Probability

variable {m x t : ℝ} {v : ℝ≥0}

/-! ### The law -/

/-- The log-normal law with log-mean `m` and log-variance `v`: the law of `exp X` when `X` is
Gaussian with mean `m` and variance `v`. -/
def logNormalMeasure (m : ℝ) (v : ℝ≥0) : Measure ℝ :=
  (gaussianReal m v).map Real.exp

/-- The log-normal law is the pushforward of a Gaussian law along `Real.exp`. -/
theorem logNormalMeasure_map_exp (m : ℝ) (v : ℝ≥0) :
    logNormalMeasure m v = (gaussianReal m v).map Real.exp := by
  rw [logNormalMeasure]

instance isProbabilityMeasure_logNormalMeasure (m : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (logNormalMeasure m v) := by
  rw [logNormalMeasure_map_exp]
  infer_instance

/-- At the singular boundary `v = 0` the log-normal law is the Dirac mass at `exp m`. -/
@[simp]
theorem logNormalMeasure_zero_var (m : ℝ) : logNormalMeasure m 0 = Measure.dirac (Real.exp m) := by
  rw [logNormalMeasure_map_exp, gaussianReal_zero_var, Measure.map_dirac' measurable_exp]

/-- The log-normal law gives no mass to the nonpositive half-line. -/
@[simp]
theorem logNormalMeasure_Iic_zero (m : ℝ) (v : ℝ≥0) : logNormalMeasure m v (Iic 0) = 0 := by
  have h : Real.exp ⁻¹' Iic (0 : ℝ) = ∅ := by
    ext y
    simp [(Real.exp_pos y).not_ge]
  rw [logNormalMeasure_map_exp, Measure.map_apply measurable_exp measurableSet_Iic, h,
    measure_empty]

/-- A log-normal variable is almost surely positive. -/
theorem ae_pos_logNormalMeasure (m : ℝ) (v : ℝ≥0) : ∀ᵐ x ∂logNormalMeasure m v, 0 < x := by
  rw [ae_iff]
  simpa only [not_lt, ← Iic_def] using logNormalMeasure_Iic_zero m v

/-! ### The density -/

/-- The density of the log-normal law with log-mean `m` and log-variance `v`, as a real-valued
function. It vanishes on the nonpositive half-line, which carries no mass. -/
def logNormalPDFReal (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else (x * √(2 * π * v))⁻¹ * Real.exp (-(Real.log x - m) ^ 2 / (2 * v))

/-- The density of the log-normal law, as a function valued in `ℝ≥0∞`. -/
def logNormalPDF (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (logNormalPDFReal m v x)

/-- The log-normal density vanishes off the positive half-line. -/
@[simp]
theorem logNormalPDFReal_of_nonpos (hx : x ≤ 0) (m : ℝ) (v : ℝ≥0) :
    logNormalPDFReal m v x = 0 := by
  rw [logNormalPDFReal, ite_eq_left hx]

/-- On the positive half-line the log-normal density is the stated formula. -/
@[simp]
theorem logNormalPDFReal_of_pos (hx : 0 < x) (m : ℝ) (v : ℝ≥0) :
    logNormalPDFReal m v x = (x * √(2 * π * v))⁻¹ * Real.exp (-(Real.log x - m) ^ 2 / (2 * v)) := by
  rw [logNormalPDFReal, ite_eq_right (not_le.mpr hx)]

/-- The `ℝ≥0∞`-valued log-normal density vanishes off the positive half-line. -/
@[simp]
theorem logNormalPDF_of_nonpos (hx : x ≤ 0) (m : ℝ) (v : ℝ≥0) :
    logNormalPDF m v x = 0 := by
  rw [logNormalPDF, logNormalPDFReal_of_nonpos hx, ENNReal.ofReal_zero]

/-- On the positive half-line the `ℝ≥0∞`-valued log-normal density is the stated formula. -/
@[simp]
theorem logNormalPDF_of_pos (hx : 0 < x) (m : ℝ) (v : ℝ≥0) :
    logNormalPDF m v x =
      ENNReal.ofReal ((x * √(2 * π * v))⁻¹ * Real.exp (-(Real.log x - m) ^ 2 / (2 * v))) := by
  rw [logNormalPDF, logNormalPDFReal_of_pos hx]

/-- The log-normal density is the Gaussian density at `log x`, scaled by `x⁻¹`: this is the
Jacobian factor of the exponential change of variables. -/
theorem logNormalPDFReal_eq_gaussianPDFReal (hx : 0 < x) (m : ℝ) (v : ℝ≥0) :
    logNormalPDFReal m v x = x⁻¹ * gaussianPDFReal m v (Real.log x) := by
  rw [logNormalPDFReal_of_pos hx]
  simp only [gaussianPDFReal_def, mul_inv]
  ring

theorem logNormalPDFReal_nonneg (m : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ logNormalPDFReal m v x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [logNormalPDFReal_of_nonpos hx]
  · rw [logNormalPDFReal_eq_gaussianPDFReal hx]
    exact mul_nonneg (inv_nonneg.mpr hx.le) (gaussianPDFReal_nonneg m v _)

@[simp]
theorem toReal_logNormalPDF (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    (logNormalPDF m v x).toReal = logNormalPDFReal m v x := by
  rw [logNormalPDF, ENNReal.toReal_ofReal (logNormalPDFReal_nonneg m v x)]

@[fun_prop]
theorem measurable_logNormalPDFReal (m : ℝ) (v : ℝ≥0) : Measurable (logNormalPDFReal m v) := by
  have h : logNormalPDFReal m v = fun x =>
      if x ≤ 0 then 0 else (x * √(2 * π * v))⁻¹ * Real.exp (-(Real.log x - m) ^ 2 / (2 * v)) := by
    ext x
    rw [logNormalPDFReal]
  rw [h]
  exact Measurable.ite measurableSet_Iic measurable_const (by fun_prop)

@[fun_prop]
theorem measurable_logNormalPDF (m : ℝ) (v : ℝ≥0) : Measurable (logNormalPDF m v) := by
  unfold logNormalPDF
  exact (measurable_logNormalPDFReal m v).ennreal_ofReal

/-- The log-normal density is supported on the positive half-line. -/
theorem indicator_Ioi_logNormalPDF (m : ℝ) (v : ℝ≥0) :
    (Ioi (0 : ℝ)).indicator (logNormalPDF m v) = logNormalPDF m v := by
  ext x
  simp only [Set.indicator_apply, Set.mem_Ioi]
  rcases le_or_gt x 0 with hx | hx
  · rw [ite_eq_right (not_lt.mpr hx), logNormalPDF, logNormalPDFReal_of_nonpos hx,
      ENNReal.ofReal_zero]
  · rw [ite_eq_left hx]

/-- The Jacobian identity behind the change of variables: the exponential of the Gaussian density
is the log-normal density weighted by the derivative of `exp`. -/
private lemma ofReal_abs_exp_mul_logNormalPDF (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    ENNReal.ofReal |Real.exp x| * logNormalPDF m v (Real.exp x) = gaussianPDF m v x := by
  rw [abs_of_pos (Real.exp_pos x), logNormalPDF, gaussianPDF,
    ← ENNReal.ofReal_mul (Real.exp_nonneg x),
    logNormalPDFReal_eq_gaussianPDFReal (Real.exp_pos x), Real.log_exp, ← mul_assoc,
    mul_inv_cancel₀ (Real.exp_ne_zero x), one_mul]

/-- **The density of the log-normal law.** For nonzero log-variance the law is
`volume.withDensity logNormalPDF`. -/
theorem logNormalMeasure_eq_withDensity (m : ℝ) (hv : v ≠ 0) :
    logNormalMeasure m v = volume.withDensity (logNormalPDF m v) := by
  ext s hs
  have hpre : MeasurableSet (Real.exp ⁻¹' s) := measurable_exp hs
  have himage : Real.exp '' (Real.exp ⁻¹' s) = Ioi 0 ∩ s := by
    rw [Set.image_preimage_eq_inter_range, Real.range_exp, Set.inter_comm]
  calc logNormalMeasure m v s
      = ∫⁻ y in Real.exp ⁻¹' s, gaussianPDF m v y := by
        rw [logNormalMeasure_map_exp, Measure.map_apply measurable_exp hs,
          gaussianReal_of_var_ne_zero m hv, withDensity_apply _ hpre]
    _ = ∫⁻ y in Real.exp ⁻¹' s, ENNReal.ofReal |Real.exp y| * logNormalPDF m v (Real.exp y) := by
        simp only [ofReal_abs_exp_mul_logNormalPDF]
    _ = ∫⁻ y in Ioi 0 ∩ s, logNormalPDF m v y := by
        rw [← himage,
          lintegral_image_eq_lintegral_abs_deriv_mul hpre
            (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn]
    _ = volume.withDensity (logNormalPDF m v) s := by
        rw [withDensity_apply _ hs, ← setLIntegral_indicator measurableSet_Ioi,
          indicator_Ioi_logNormalPDF]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a log-normal law of nonzero log-variance has a density. -/
theorem hasPDF_of_hasLaw_logNormalMeasure (hv : v ≠ 0) (hX : HasLaw X (logNormalMeasure m v) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_logNormalPDF m v).aemeasurable
    (by rwa [logNormalMeasure_eq_withDensity m hv] at hX)

/-- The density of a log-normal law is `logNormalPDF`. -/
theorem pdf_eq_logNormalPDF_of_hasLaw_logNormalMeasure (hv : v ≠ 0)
    (hX : HasLaw X (logNormalMeasure m v) P) : pdf X P volume =ᵐ[volume] logNormalPDF m v :=
  pdf_eq_of_hasLaw_withDensity (measurable_logNormalPDF m v).aemeasurable
    (by rwa [logNormalMeasure_eq_withDensity m hv] at hX)

/-- The Radon–Nikodym derivative of a log-normal law against Lebesgue measure is
`logNormalPDF`. -/
theorem rnDeriv_logNormalMeasure (m : ℝ) (hv : v ≠ 0) :
    (logNormalMeasure m v).rnDeriv volume =ᵐ[volume] logNormalPDF m v := by
  rw [logNormalMeasure_eq_withDensity m hv]
  exact Measure.rnDeriv_withDensity volume (measurable_logNormalPDF m v)

/-! ### The cumulative distribution function -/

/-- **The cumulative distribution function of the log-normal law** with nonzero log-variance. -/
theorem cdf_logNormalMeasure_eq (m : ℝ) (hv : v ≠ 0) (x : ℝ) :
    cdf (logNormalMeasure m v) x =
      if x ≤ 0 then 0 else (1 + Real.erf ((Real.log x - m) / √(2 * (v : ℝ)))) / 2 := by
  rw [cdf_eq_real, measureReal_def]
  split_ifs with hx
  · rw [measure_mono_null (Iic_subset_Iic.mpr hx) (logNormalMeasure_Iic_zero m v),
      ENNReal.toReal_zero]
  · have hpre : Real.exp ⁻¹' Iic x = Iic (Real.log x) := by
      ext y
      simp [Real.le_log_iff_exp_le (not_le.mp hx)]
    rw [logNormalMeasure_map_exp, Measure.map_apply measurable_exp measurableSet_Iic, hpre,
      ← measureReal_def, ← cdf_eq_real]
    exact cdf_gaussianReal_eq m hv (Real.log x)

/-- At the singular boundary `v = 0` the cdf of the log-normal law is a step function. -/
theorem cdf_logNormalMeasure_zero_var (m x : ℝ) :
    cdf (logNormalMeasure m 0) x = if Real.exp m ≤ x then 1 else 0 := by
  rw [logNormalMeasure_zero_var, cdf_dirac]

/-! ### Moments -/

/-- Every power of a log-normal variable is integrable. -/
theorem integrable_pow_logNormalMeasure (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x => x ^ n) (logNormalMeasure m v) := by
  rw [logNormalMeasure_map_exp,
    integrable_map_measure (by fun_prop) measurable_exp.aemeasurable]
  simpa only [Function.comp_def, Real.exp_nat_mul] using
    integrable_exp_mul_gaussianReal (μ := m) (v := v) n

/-- **The raw moments of the log-normal law.** They are the Gaussian moment-generating function
evaluated at natural numbers, and the formula is valid at the boundary `v = 0` as well. -/
theorem integral_pow_logNormalMeasure (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    ∫ x, x ^ n ∂logNormalMeasure m v = Real.exp ((n : ℝ) * m + (n : ℝ) ^ 2 * (v : ℝ) / 2) := by
  rw [logNormalMeasure_map_exp, integral_map measurable_exp.aemeasurable (by fun_prop)]
  have h : ∫ y, Real.exp y ^ n ∂gaussianReal m v = mgf id (gaussianReal m v) n := by
    rw [mgf]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [id_eq]
    rw [← Real.exp_nat_mul]
  rw [h, mgf_id_gaussianReal]
  ring_nf

/-- The mean of the log-normal law is `exp (m + v / 2)`. -/
theorem integral_id_logNormalMeasure (m : ℝ) (v : ℝ≥0) :
    ∫ x, x ∂logNormalMeasure m v = Real.exp (m + (v : ℝ) / 2) := by
  simpa using integral_pow_logNormalMeasure m v 1

/-- The second raw moment of the log-normal law is `exp (2 * m + 2 * v)`. -/
theorem integral_sq_logNormalMeasure (m : ℝ) (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂logNormalMeasure m v = Real.exp (2 * m + 2 * (v : ℝ)) := by
  rw [integral_pow_logNormalMeasure m v 2]
  congr 1
  push_cast
  ring

/-- The variance of the log-normal law is `(exp v - 1) * exp (2 * m + v)`; at the boundary `v = 0`
this is `0`, as it must be for a Dirac mass. -/
theorem variance_id_logNormalMeasure (m : ℝ) (v : ℝ≥0) :
    Var[id; logNormalMeasure m v] = (Real.exp (v : ℝ) - 1) * Real.exp (2 * m + (v : ℝ)) := by
  have hLp : MemLp id 2 (logNormalMeasure m v) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using integrable_pow_logNormalMeasure m v 2)
  rw [variance_eq_sub hLp]
  have h₂ : (logNormalMeasure m v)[(id : ℝ → ℝ) ^ 2] = Real.exp (2 * m + 2 * (v : ℝ)) := by
    simpa using integral_sq_logNormalMeasure m v
  have h₁ : (logNormalMeasure m v)[(id : ℝ → ℝ)] = Real.exp (m + (v : ℝ) / 2) := by
    simpa using integral_id_logNormalMeasure m v
  have hMeanExponent : ((2 : ℕ) : ℝ) * (m + (v : ℝ) / 2) = 2 * m + (v : ℝ) := by
    push_cast
    ring
  have hSecondExponent : 2 * m + 2 * (v : ℝ) = (v : ℝ) + (2 * m + (v : ℝ)) := by
    ring
  rw [h₂, h₁, ← Real.exp_nat_mul (m + (v : ℝ) / 2) 2, hMeanExponent, hSecondExponent,
    Real.exp_add]
  ring

/-! ### Exponential moments -/

/-- For nonpositive `t` the moment-generating integrand of a log-normal law is bounded by `1` on
the support, hence integrable. -/
theorem integrable_exp_mul_logNormalMeasure (m : ℝ) (v : ℝ≥0) (ht : t ≤ 0) :
    Integrable (fun x => Real.exp (t * x)) (logNormalMeasure m v) := by
  refine Integrable.mono' (integrable_const 1) (by fun_prop) ?_
  filter_upwards [ae_pos_logNormalMeasure m v] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  nlinarith [hx.le]

/-- The growth statement behind the failure of the positive exponential moments: against the
Gaussian exponent `-(x - m) ^ 2 / (2 * v)`, the term `t * exp x` wins for every `t > 0`. -/
private lemma tendsto_mul_exp_sub_sq_atTop (m : ℝ) {w t : ℝ} (hw : 0 < w) (ht : 0 < t) :
    Tendsto (fun x => t * Real.exp x - (x - m) ^ 2 / (2 * w)) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => (x - m) ^ 2 * Real.exp (-(x - m))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
      (tendsto_atTop_add_const_right atTop (-m) tendsto_id)
    simpa only [Function.comp_def, id_eq, ← sub_eq_add_neg] using h
  have h1 : Tendsto (fun x : ℝ => (x - m) ^ 2 / (2 * w * Real.exp x)) atTop (𝓝 0) := by
    have heq : ∀ x : ℝ, (x - m) ^ 2 / (2 * w * Real.exp x)
        = (x - m) ^ 2 * Real.exp (-(x - m)) * (Real.exp (-m) / (2 * w)) := by
      intro x
      rw [Real.exp_neg, Real.exp_neg, Real.exp_sub]
      field_simp
    simp_rw [heq]
    simpa using h0.mul_const (Real.exp (-m) / (2 * w))
  have h2 : Tendsto (fun x : ℝ => Real.exp x * (t - (x - m) ^ 2 / (2 * w * Real.exp x)))
      atTop atTop :=
    Filter.Tendsto.atTop_mul_pos ht Real.tendsto_exp_atTop
      (by simpa using tendsto_const_nhds.sub h1)
  refine h2.congr fun x => ?_
  have hx : Real.exp x ≠ 0 := Real.exp_ne_zero x
  field_simp

/-- **The positive exponential moments of a log-normal law do not exist.** -/
theorem not_integrable_exp_mul_logNormalMeasure (m : ℝ) (hv : v ≠ 0) (ht : 0 < t) :
    ¬ Integrable (fun x => Real.exp (t * x)) (logNormalMeasure m v) := by
  have hw : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [logNormalMeasure_map_exp,
    integrable_map_measure (by fun_prop) measurable_exp.aemeasurable,
    gaussianReal_of_var_ne_zero m hv,
    integrable_withDensity_iff (measurable_gaussianPDF m v) (ae_of_all _ fun _ => by
      simp [gaussianPDF])]
  intro hint
  simp only [Function.comp_def] at hint
  -- The integrand is eventually at least `1`, on a half-line of infinite Lebesgue measure.
  have hpos : 0 < √(2 * π * (v : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hev : ∀ᶠ x in atTop,
      (1 : ℝ) ≤ Real.exp (t * Real.exp x) * (gaussianPDF m v x).toReal := by
    filter_upwards [(tendsto_mul_exp_sub_sq_atTop m hw ht).eventually_ge_atTop
      (Real.log √(2 * π * (v : ℝ)))] with x hx
    have key : √(2 * π * (v : ℝ))
        ≤ Real.exp (t * Real.exp x) * Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ))) := by
      rw [← Real.exp_add, ← Real.exp_log hpos]
      refine Real.exp_le_exp.mpr ?_
      rw [neg_div]
      linarith
    rw [toReal_gaussianPDF]
    simp only [gaussianPDFReal_def]
    calc (1 : ℝ) = (√(2 * π * (v : ℝ)))⁻¹ * √(2 * π * (v : ℝ)) := by
          rw [inv_mul_cancel₀ hpos.ne']
      _ ≤ (√(2 * π * (v : ℝ)))⁻¹
            * (Real.exp (t * Real.exp x) * Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ)))) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = Real.exp (t * Real.exp x)
            * ((√(2 * π * (v : ℝ)))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ)))) := by ring
  obtain ⟨a, ha⟩ := eventually_atTop.mp hev
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi a) volume := by
    refine Integrable.mono' hint.integrableOn (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_one]
    exact ha x hx.le
  rw [integrableOn_const_iff] at hone
  simp [Real.volume_Ioi] at hone

/-- **The exponential-integrability domain of a log-normal law with nonzero log-variance is the
nonpositive half-line.** -/
theorem integrableExpSet_id_logNormalMeasure (m : ℝ) (hv : v ≠ 0) :
    integrableExpSet id (logNormalMeasure m v) = Iic 0 := by
  ext u
  simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq, mem_Iic]
  exact ⟨fun h => not_lt.mp fun hu => not_integrable_exp_mul_logNormalMeasure m hv hu h,
    integrable_exp_mul_logNormalMeasure m v⟩

/-! ### Boundary transforms -/

/-- Every exponential moment exists at the singular boundary `v = 0`. -/
theorem integrableExpSet_id_logNormalMeasure_zero_var (m : ℝ) :
    integrableExpSet id (logNormalMeasure m 0) = univ := by
  rw [logNormalMeasure_zero_var]
  exact integrableExpSet_dirac _ _

/-- The moment-generating function at the singular boundary `v = 0`. -/
theorem mgf_id_logNormalMeasure_zero_var (m t : ℝ) :
    mgf id (logNormalMeasure m 0) t = Real.exp (t * Real.exp m) := by
  rw [logNormalMeasure_zero_var, mgf_dirac']
  rfl

/-- The cumulant-generating function at the singular boundary `v = 0`. -/
theorem cgf_id_logNormalMeasure_zero_var (m t : ℝ) :
    cgf id (logNormalMeasure m 0) t = t * Real.exp m := by
  rw [logNormalMeasure_zero_var, cgf_dirac']
  rfl

/-- The characteristic function at the singular boundary `v = 0`. -/
theorem charFun_logNormalMeasure_zero_var (m t : ℝ) :
    charFun (logNormalMeasure m 0) t = Complex.exp (Complex.I * (t : ℂ) * Real.exp m) := by
  rw [logNormalMeasure_zero_var, charFun_dirac]
  congr 1
  simp only [RCLike.inner_apply, conj_trivial, Complex.ofReal_mul]
  ring

/-! ### Parameter measurability -/

/-- The log-normal family is measurable in its parameters, so it can be used as a kernel. -/
theorem measurable_logNormalMeasure :
    Measurable fun p : ℝ × ℝ≥0 => logNormalMeasure p.1 p.2 := by
  simp only [logNormalMeasure_map_exp]
  exact (Measure.measurable_map _ measurable_exp).comp measurable_gaussianReal

end Probability

end TauCeti
