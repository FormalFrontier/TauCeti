/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.HasLaw
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta
public import TauCeti.Probability.Distributions.Beta.Basic

/-!
# The cumulative distribution function of a beta law

This file computes `ProbabilityTheory.cdf (betaMeasure α β)` in closed form: for positive shape
parameters it is the regularized incomplete beta function `TauCeti.regularizedIncompleteBeta`,
`I_x(α, β)`.

This is the beta entry of the closed-form cdf target of
`TauCetiRoadmap/StandardDistributions/README.md`, Layer 2.

The identity holds for every real `x`, with no constraint to the unit interval: outside `[0, 1]`
both sides are constant, because `TauCeti.regularizedIncompleteBeta` clamps its argument there.
That agreement at the clamping convention is the reason the roadmap prescribes the totalization
it does.

The proof splits `Set.Iic x` at the two ends of the support. Below the origin the density
vanishes, so the cdf is `0`; on `[0, 1]` the cdf integral is exactly the normalized beta integral
defining `I_x(α, β)`; and above `1` the extra piece contributes nothing, so the value is Euler's
integral divided by itself, namely `1`.

## Main results

* `TauCeti.cdf_betaMeasure_eq` — the closed-form cdf `I_x(α, β)`;
* `TauCeti.measureReal_Iic_betaMeasure` — the same in measure form;
* `TauCeti.measureReal_Ioc_betaMeasure` — the mass of a bounded interval, as a difference of two
  values of `I_·(α, β)`;
* `TauCeti.measureReal_Ioi_betaMeasure` — the upper tail `1 - I_x(α, β)`;
* `TauCeti.continuous_cdf_betaMeasure` — the cdf is continuous, so a beta law has no atoms;
* `TauCeti.measureReal_le_of_hasLaw_betaMeasure` — the random-variable corollary.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 2, the "Closed-form cdfs and
  tails" target.
* Formal template: `TauCeti/Probability/Distributions/Gamma/Cdf.lean`.
* *NIST Digital Library of Mathematical Functions*, [§8.17](https://dlmf.nist.gov/8.17).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

variable {α β x : ℝ}

/-! ### The cdf as an integral of the density -/

/-- The beta density is integrable: it is a nonnegative function whose Lebesgue integral is `1`. -/
private lemma integrable_betaPDFReal (hα : 0 < α) (hβ : 0 < β) :
    Integrable (betaPDFReal α β) := by
  refine ⟨(measurable_betaPDFReal α β).aestronglyMeasurable, ?_⟩
  have h : ∫⁻ y, ENNReal.ofReal (betaPDFReal α β y) = 1 := lintegral_betaPDF_eq_one hα hβ
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (betaPDFReal_nonneg hα hβ)), h]
  exact ENNReal.one_lt_top

/-- The cumulative distribution function of a beta law is the integral of its density over a lower
half-line. This is the beta analogue of `ProbabilityTheory.cdf_gammaMeasure_eq_integral`. -/
private lemma cdf_betaMeasure_eq_integral (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    cdf (betaMeasure α β) x = ∫ t in Iic x, betaPDFReal α β t := by
  have hp : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  rw [cdf_eq_real, betaMeasure, measureReal_def, withDensity_apply _ measurableSet_Iic]
  simp only [betaPDF]
  refine (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (betaPDFReal_nonneg hα hβ)) ?_).symm
  exact (measurable_betaPDFReal α β).aestronglyMeasurable

/-! ### The three ranges of the support -/

/-- Below the origin the beta density integrates to `0`. -/
private lemma setIntegral_betaPDFReal_Iic_of_nonpos (α β : ℝ) (hx : x ≤ 0) :
    ∫ t in Iic x, betaPDFReal α β t = 0 := by
  exact setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ by
    rw [betaPDFReal, ite_eq_right fun ht' ↦ absurd ht'.1 (not_lt.mpr (ht.trans hx))]

/-- On the support the beta density is the beta integrand divided by `Β(α, β)`, so on `[0, 1]` the
cdf integral is the normalized integral defining `I_x(α, β)`. -/
private lemma setIntegral_betaPDFReal_Iic_of_mem_Icc (hα : 0 < α) (hβ : 0 < β) (hx₀ : 0 ≤ x)
    (hx₁ : x ≤ 1) :
    ∫ t in Iic x, betaPDFReal α β t =
      (∫ t in (0 : ℝ)..x, t ^ (α - 1) * (1 - t) ^ (β - 1)) / beta α β := by
  have hint := integrable_betaPDFReal hα hβ
  have hdens : ∀ t ∈ Ioo (0 : ℝ) x,
      betaPDFReal α β t = (1 / beta α β) * (t ^ (α - 1) * (1 - t) ^ (β - 1)) := by
    intro t ht
    rw [betaPDFReal, ite_eq_left ⟨ht.1, ht.2.trans_le hx₁⟩]
    ring
  rw [← Iic_union_Ioc_eq_Iic hx₀, setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      hint.integrableOn hint.integrableOn,
    setIntegral_betaPDFReal_Iic_of_nonpos α β le_rfl, zero_add, integral_Ioc_eq_integral_Ioo,
    -- `hdens` fails at `t = x = 1`: there `betaPDFReal` is zero, but `0 ^ (β - 1)` is
    -- one when `β = 1`, so drop the endpoint.
    setIntegral_congr_fun measurableSet_Ioo hdens, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hx₀, intervalIntegral.integral_const_mul]
  ring

/-- Above the support the beta density contributes nothing, so the cdf integral is Euler's beta
integral divided by `Β(α, β)`, namely `1`. -/
private lemma setIntegral_betaPDFReal_Iic_of_one_le (hα : 0 < α) (hβ : 0 < β) (hx : 1 ≤ x) :
    ∫ t in Iic x, betaPDFReal α β t = 1 := by
  have hint := integrable_betaPDFReal hα hβ
  have hzero : ∀ t ∈ Ioc (1 : ℝ) x, betaPDFReal α β t = 0 := by
    intro t ht
    rw [betaPDFReal, ite_eq_right fun ht' => absurd ht'.2 (not_lt.mpr ht.1.le)]
  rw [← Iic_union_Ioc_eq_Iic hx, setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      hint.integrableOn hint.integrableOn,
    setIntegral_congr_fun measurableSet_Ioc hzero, integral_zero, add_zero,
    setIntegral_betaPDFReal_Iic_of_mem_Icc hα hβ zero_le_one le_rfl,
    integral_rpow_mul_one_sub_rpow hα hβ, div_self (beta_pos hα hβ).ne']

/-! ### The closed form -/

/-- The cumulative distribution function of the beta law with positive shape parameters `α` and
`β` is the regularized incomplete beta function, `I_x(α, β)`.

No constraint on `x` is needed: outside `[0, 1]` both sides are constant, which is exactly the
clamping convention built into `TauCeti.regularizedIncompleteBeta`. -/
@[simp]
theorem cdf_betaMeasure_eq (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    cdf (betaMeasure α β) x = regularizedIncompleteBeta α β x := by
  rw [cdf_betaMeasure_eq_integral hα hβ]
  rcases le_or_gt x 0 with hx | hx
  · rw [setIntegral_betaPDFReal_Iic_of_nonpos α β hx,
      regularizedIncompleteBeta_eq_zero_of_nonpos hα.ne' β hx]
  rcases le_or_gt x 1 with hx₁ | hx₁
  · rw [setIntegral_betaPDFReal_Iic_of_mem_Icc hα hβ hx.le hx₁,
      regularizedIncompleteBeta_def_of_mem_Icc hα hβ ⟨hx.le, hx₁⟩]
  · rw [setIntegral_betaPDFReal_Iic_of_one_le hα hβ hx₁.le,
      regularizedIncompleteBeta_eq_one_of_one_le hα.le hβ hx₁.le]

/-! ### Consequences -/

/-- The mass a beta law assigns to a lower half-line, in measure form. -/
@[simp]
theorem measureReal_Iic_betaMeasure (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    (betaMeasure α β).real (Iic x) = regularizedIncompleteBeta α β x := by
  have hp : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  rw [← cdf_eq_real]
  exact cdf_betaMeasure_eq hα hβ x

/-- The mass a beta law assigns to a bounded interval is the increment of `I_·(α, β)`. -/
@[simp]
theorem measureReal_Ioc_betaMeasure (hα : 0 < α) (hβ : 0 < β) {y : ℝ} (hyx : y ≤ x) :
    (betaMeasure α β).real (Ioc y x) =
      regularizedIncompleteBeta α β x - regularizedIncompleteBeta α β y := by
  have hp : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  have hunion : (betaMeasure α β).real (Iic y) + (betaMeasure α β).real (Ioc y x) =
      (betaMeasure α β).real (Iic x) := by
    rw [← measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc, Iic_union_Ioc_eq_Iic hyx]
  rw [measureReal_Iic_betaMeasure hα hβ x, measureReal_Iic_betaMeasure hα hβ y] at hunion
  linarith

/-- The upper tail of a beta law is `1 - I_x(α, β)`. -/
@[simp]
theorem measureReal_Ioi_betaMeasure (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    (betaMeasure α β).real (Ioi x) = 1 - regularizedIncompleteBeta α β x := by
  have hp : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, measureReal_Iic_betaMeasure hα hβ]
  simp

/-- The cumulative distribution function of a beta law is continuous: `I_·(α, β)` is continuous
even at the two endpoints of the support, where for `α < 1` or `β < 1` the beta integrand blows
up. -/
theorem continuous_cdf_betaMeasure (hα : 0 < α) (hβ : 0 < β) :
    Continuous (cdf (betaMeasure α β)) := by
  have h : ⇑(cdf (betaMeasure α β)) = regularizedIncompleteBeta α β :=
    funext (cdf_betaMeasure_eq hα hβ)
  rw [h]
  exact continuous_regularizedIncompleteBeta hα hβ

/-- A random variable with a beta law has the regularized incomplete beta function as its
cumulative distribution function. -/
theorem measureReal_le_of_hasLaw_betaMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hα : 0 < α) (hβ : 0 < β) (hX : HasLaw X (betaMeasure α β) P) (x : ℝ) :
    P.real {ω | X ω ≤ x} = regularizedIncompleteBeta α β x := by
  rw [hX.measureReal_eq (p := fun y : ℝ => y ≤ x) measurableSet_Iic, Set.Iic_def]
  exact measureReal_Iic_betaMeasure hα hβ x

end TauCeti
