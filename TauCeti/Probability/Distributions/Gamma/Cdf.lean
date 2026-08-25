/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma
public import TauCeti.Probability.Distributions.Gamma.Basic

/-!
# The cumulative distribution function of a gamma law

This file computes `ProbabilityTheory.cdf (gammaMeasure a r)` in closed form: for a positive
shape `a` and a positive rate `r` it is the regularized lower incomplete gamma function
`TauCeti.regularizedGamma` read at the rate-scaled point, `P(a, r * x)`.

This is the gamma entry of the closed-form cdf target of
`TauCetiRoadmap/StandardDistributions/README.md`, Layer 2.

The identity holds for every real `x`, with no sign hypothesis: below the support both sides
vanish, because `TauCeti.regularizedGamma` is extended by `0` there. That agreement at the
clamping convention is the reason the roadmap prescribes the totalizations it does.

The computation is one change of variables. Mathlib's
`ProbabilityTheory.cdf_gammaMeasure_eq_integral` presents the cdf as the integral of
`gammaPDFReal a r` over `Set.Iic x`; the density vanishes below
the origin, so for `0 < x` that integral is the interval integral over `0..x`. Collecting the rate
into the variable, the integrand becomes `Γ(a)⁻¹ * r * ((r * t) ^ (a - 1) * exp (-(r * t)))`, so
`intervalIntegral.integral_comp_mul_left` at `c = r` turns it into
`Γ(a)⁻¹ * ∫ u in 0..r * x, u ^ (a - 1) * exp (-u)`, which is `P(a, r * x)` by definition.

At shape `a = 1` the result recovers Mathlib's `ProbabilityTheory.cdf_expMeasure_eq`, since
`ProbabilityTheory.expMeasure r` is `gammaMeasure 1 r` and
`TauCeti.regularizedGamma_one` evaluates `P(1, y)` as `1 - exp (-y)`; this is the exponential
completion check of the same layer.

## Main results

* `TauCeti.cdf_gammaMeasure_eq` — the closed-form cdf `P(a, r * x)`;
* `TauCeti.measureReal_Iic_gammaMeasure` — the same in measure form;
* `TauCeti.measureReal_Ioc_gammaMeasure` — the mass of a bounded interval, as a difference of two
  values of `P(a, ·)`;
* `TauCeti.measureReal_Ioi_gammaMeasure` — the upper tail `1 - P(a, r * x)`;
* `TauCeti.continuous_cdf_gammaMeasure` — the cdf is continuous, so a gamma law has no atoms;
* `TauCeti.measureReal_le_of_hasLaw_gammaMeasure` — the random-variable corollary.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 2, the "Closed-form cdfs and
  tails" target.
* *NIST Digital Library of Mathematical Functions*, [§8.2](https://dlmf.nist.gov/8.2).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti

variable {a r x : ℝ}

/-! ### Reduction of the cdf integral to the positive half-line -/

/-- The gamma density is integrable: it is a nonnegative function whose Lebesgue integral is `1`. -/
private lemma integrable_gammaPDFReal (ha : 0 < a) (hr : 0 < r) :
    Integrable (gammaPDFReal a r) := by
  refine ⟨(measurable_gammaPDFReal a r).aestronglyMeasurable, ?_⟩
  have h : ∫⁻ y, ENNReal.ofReal (gammaPDFReal a r y) = 1 := lintegral_gammaPDF_eq_one ha hr
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gammaPDFReal_nonneg ha hr)), h]
  exact ENNReal.one_lt_top

/-- Below the origin the gamma density integrates to `0`. -/
private lemma setIntegral_gammaPDFReal_Iic_of_nonpos (a r : ℝ) (hx : x ≤ 0) :
    ∫ t in Iic x, gammaPDFReal a r t = 0 := by
  have h : ∀ t ∈ Iio x, gammaPDFReal a r t = 0 := by
    intro t ht
    rw [gammaPDFReal, ite_eq_right (not_le.mpr (ht.trans_le hx))]
  rw [integral_Iic_eq_integral_Iio, setIntegral_congr_fun measurableSet_Iio h, integral_zero]

/-- Collecting the rate into the integration variable: on the positive half-line the gamma density
is `Γ(a)⁻¹ * r` times Euler's integrand evaluated at `r * t`. -/
private lemma gammaPDFReal_eq_comp_mul (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    gammaPDFReal a r t =
      (Real.Gamma a)⁻¹ * r * ((r * t) ^ (a - 1) * Real.exp (-(r * t))) := by
  have hrpow : r * r ^ (a - 1) = r ^ a := by
    have h := Real.rpow_add hr 1 (a - 1)
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  rw [gammaPDFReal, ite_eq_left ht.le, Real.mul_rpow hr.le ht.le, ← hrpow]
  ring

/-! ### The closed form -/

/-- The cumulative distribution function of the gamma law with shape `a` and rate `r` is the
regularized lower incomplete gamma function evaluated at the rate-scaled point,
`P(a, r * x)`.

No sign hypothesis on `x` is needed: below the support both sides are `0`, which is exactly the
clamping convention built into `TauCeti.regularizedGamma`. -/
@[simp]
theorem cdf_gammaMeasure_eq (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    cdf (gammaMeasure a r) x = regularizedGamma a (r * x) := by
  have hr0 : r ≠ 0 := hr.ne'
  rw [cdf_gammaMeasure_eq_integral ha hr]
  rcases le_or_gt x 0 with hx | hx
  · rw [setIntegral_gammaPDFReal_Iic_of_nonpos a r hx,
      regularizedGamma_eq_zero_of_nonpos_right a (mul_nonpos_of_nonneg_of_nonpos hr.le hx)]
  have hint := integrable_gammaPDFReal ha hr
  have hsplit : ∫ t in Iic x, gammaPDFReal a r t = ∫ t in Ioc (0 : ℝ) x, gammaPDFReal a r t := by
    rw [← Iic_union_Ioc_eq_Iic hx.le, setIntegral_union (Iic_disjoint_Ioc le_rfl)
      measurableSet_Ioc hint.integrableOn hint.integrableOn,
      setIntegral_gammaPDFReal_Iic_of_nonpos a r le_rfl, zero_add]
  have hsubst : ∫ t in (0 : ℝ)..x, (r * t) ^ (a - 1) * Real.exp (-(r * t)) =
      r⁻¹ * ∫ u in (0 : ℝ)..r * x, u ^ (a - 1) * Real.exp (-u) := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := x) (c := r)
      (fun u : ℝ => u ^ (a - 1) * Real.exp (-u)) hr0
    simpa only [mul_zero, smul_eq_mul] using h
  rw [hsplit, setIntegral_congr_fun measurableSet_Ioc
      (fun t ht => gammaPDFReal_eq_comp_mul hr ht.1),
    ← intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_const_mul, hsubst,
    ← lowerIncompleteGamma_eq_integral ha (by positivity), regularizedGamma_eq_div]
  field_simp

/-! ### Consequences -/

/-- The mass a gamma law assigns to a lower half-line, in measure form. -/
@[simp]
theorem measureReal_Iic_gammaMeasure (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    (gammaMeasure a r).real (Iic x) = regularizedGamma a (r * x) := by
  have hp : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [← cdf_eq_real]
  exact cdf_gammaMeasure_eq ha hr x

/-- The mass a gamma law assigns to a bounded interval is the increment of `P(a, r * ·)`. -/
@[simp]
theorem measureReal_Ioc_gammaMeasure (ha : 0 < a) (hr : 0 < r) {y : ℝ} (hyx : y ≤ x) :
    (gammaMeasure a r).real (Ioc y x) =
      regularizedGamma a (r * x) - regularizedGamma a (r * y) := by
  have hp : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  have hunion : (gammaMeasure a r).real (Iic y) + (gammaMeasure a r).real (Ioc y x) =
      (gammaMeasure a r).real (Iic x) := by
    rw [← measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc, Iic_union_Ioc_eq_Iic hyx]
  rw [measureReal_Iic_gammaMeasure ha hr x, measureReal_Iic_gammaMeasure ha hr y] at hunion
  linarith

/-- The upper tail of a gamma law is `1 - P(a, r * x)`. -/
@[simp]
theorem measureReal_Ioi_gammaMeasure (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    (gammaMeasure a r).real (Ioi x) = 1 - regularizedGamma a (r * x) := by
  have hp : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, measureReal_Iic_gammaMeasure ha hr]
  simp

/-- The cumulative distribution function of a gamma law is continuous: `P(a, ·)` is continuous even
at the origin, where for `a < 1` Euler's integrand blows up. -/
theorem continuous_cdf_gammaMeasure (ha : 0 < a) (hr : 0 < r) :
    Continuous (cdf (gammaMeasure a r)) := by
  have h : ⇑(cdf (gammaMeasure a r)) = fun x => regularizedGamma a (r * x) :=
    funext (cdf_gammaMeasure_eq ha hr)
  rw [h]
  fun_prop

/-- A random variable with a gamma law has the regularized lower incomplete gamma function as its
cumulative distribution function. -/
theorem measureReal_le_of_hasLaw_gammaMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (ha : 0 < a) (hr : 0 < r) (hX : HasLaw X (gammaMeasure a r) P) (x : ℝ) :
    P.real {ω | X ω ≤ x} = regularizedGamma a (r * x) := by
  rw [hX.measureReal_eq (p := fun y : ℝ => y ≤ x) measurableSet_Iic, Set.Iic_def]
  exact measureReal_Iic_gammaMeasure ha hr x

end TauCeti
