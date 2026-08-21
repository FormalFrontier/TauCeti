/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Elementary theory of the beta distribution

This file completes the elementary moment theory of Mathlib's beta distribution. For positive
shape parameters it computes every natural raw moment, and obtains the mean and variance as the
first two cases. It also records that the beta law is carried by `[0, 1]`, so every exponential
moment exists.

## Main results

* `TauCeti.integral_pow_betaMeasure` — the natural raw moments as a quotient of Gamma values;
* `TauCeti.integral_id_betaMeasure` — the mean is `α / (α + β)`;
* `TauCeti.variance_id_betaMeasure` — the variance is
  `α * β / ((α + β) ^ 2 * (α + β + 1))`;
* `TauCeti.integrableExpSet_id_betaMeasure` — every exponential moment exists.

The integral calculation follows the normalization argument for `ProbabilityTheory.betaMeasure`
in Mathlib: rewrite the density integral as Euler's beta integral, then use the Gamma quotient.

## References

* Tau Ceti roadmap, `StandardDistributions`, Layer 1, "Beta".
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

private lemma betaPDFReal_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  rw [betaPDFReal]
  split_ifs with hx
  · exact mul_nonneg (mul_nonneg (one_div_nonneg.mpr (beta_pos hα hβ).le)
      (Real.rpow_nonneg hx.1.le _))
      (Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _)
  · exact le_rfl

private lemma toReal_betaPDF {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    (ENNReal.ofReal (betaPDFReal α β x)).toReal = betaPDFReal α β x :=
  ENNReal.toReal_ofReal (betaPDFReal_nonneg hα hβ x)

/-- Euler's beta integral in real-valued form. This is the calculation used internally by the
moment formula. -/
private lemma integral_rpow_mul_one_sub_rpow {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x in Set.Ioo 0 1, x ^ (α - 1) * (1 - x) ^ (β - 1) = beta α β := by
  rw [beta_eq_betaIntegralReal α β hα hβ, Complex.betaIntegral,
    intervalIntegral.integral_of_le (by norm_num), ← integral_Ioc_eq_integral_Ioo,
    ← RCLike.re_to_complex, ← integral_re]
  · refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx0, hx1⟩ ↦ ?_
    norm_cast
    rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
      Complex.re_mul_ofReal, Complex.ofReal_re]
    all_goals linarith
  · convert! Complex.betaIntegral_convergent (u := α) (v := β) (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num), IntegrableOn]

/-- The beta distribution is carried by the unit interval. -/
theorem ae_mem_Icc_betaMeasure (α β : ℝ) :
    ∀ᵐ x ∂betaMeasure α β, x ∈ Set.Icc (0 : ℝ) 1 := by
  have hpdf : betaPDF α β = ENNReal.ofReal ∘ betaPDFReal α β := rfl
  rw [betaMeasure, hpdf, ae_withDensity_iff
    (ENNReal.measurable_ofReal.comp (measurable_betaPDFReal α β))]
  refine ae_of_all _ fun x hx ↦ ?_
  constructor
  · by_contra h
    exact hx (betaPDF_eq_zero_of_nonpos (le_of_not_ge h))
  · by_contra h
    exact hx (betaPDF_eq_zero_of_one_le (le_of_not_ge h))

/-- The `n`th raw moment of a beta distribution with positive shape parameters. -/
@[simp]
theorem integral_pow_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    ∫ x, x ^ n ∂betaMeasure α β =
      Real.Gamma (α + n) * Real.Gamma (α + β) /
        (Real.Gamma α * Real.Gamma (α + β + n)) := by
  have hαn : 0 < α + (n : ℝ) := add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg n)
  have hpdf : betaPDF α β = ENNReal.ofReal ∘ betaPDFReal α β := rfl
  rw [betaMeasure, hpdf, integral_withDensity_eq_integral_toReal_smul
    (ENNReal.measurable_ofReal.comp (measurable_betaPDFReal α β))
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) (fun x ↦ x ^ n)]
  simp_rw [Function.comp_apply, toReal_betaPDF hα hβ, smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioo (0 : ℝ) 1)]
  · calc
      ∫ x in Set.Ioo 0 1, betaPDFReal α β x * x ^ n =
          ∫ x in Set.Ioo 0 1,
            (1 / beta α β) * (x ^ (α + n - 1) * (1 - x) ^ (β - 1)) := by
        refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
        rw [betaPDFReal, ite_eq_left ⟨hx.1, hx.2⟩]
        calc
          ((1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)) * x ^ n =
              (1 / beta α β) *
                ((x ^ n * x ^ (α - 1)) * (1 - x) ^ (β - 1)) := by ring_nf
          _ = (1 / beta α β) *
                (x ^ (α + n - 1) * (1 - x) ^ (β - 1)) := by
            rw [← Real.rpow_natCast x n, ← Real.rpow_add hx.1]
            congr 3
            ring_nf
      _ = (1 / beta α β) * beta (α + n) β := by
        rw [integral_const_mul, integral_rpow_mul_one_sub_rpow hαn hβ]
      _ = Real.Gamma (α + n) * Real.Gamma (α + β) /
            (Real.Gamma α * Real.Gamma (α + β + n)) := by
        rw [beta, beta]
        field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα),
          ne_of_gt (Real.Gamma_pos_of_pos hβ),
          ne_of_gt (Real.Gamma_pos_of_pos hαn),
          ne_of_gt (Real.Gamma_pos_of_pos (add_pos hα hβ)),
          ne_of_gt (Real.Gamma_pos_of_pos (add_pos hαn hβ))]
        ring_nf
  · intro x hx
    rw [betaPDFReal]
    split_ifs with h
    · exact (hx h).elim
    · simp

/-- `Real.Gamma` two steps up: `Γ (x + 2) = (x + 1) * x * Γ x`. The second raw moment of a beta
law evaluates `Real.Gamma` at `α + 2` and at `α + β + 2`, and this is the shape in which those two
values are compared with `Real.Gamma α` and `Real.Gamma (α + β)`. -/
private lemma Gamma_add_two {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 2) = (x + 1) * x * Real.Gamma x := by
  have hx2 : x + 2 = x + 1 + 1 := by ring
  rw [hx2, Real.Gamma_add_one (by linarith : (0 : ℝ) < x + 1).ne',
    Real.Gamma_add_one hx.ne']
  ring

/-- The mean of a beta distribution with positive shape parameters. -/
@[simp]
theorem integral_id_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, x ∂betaMeasure α β = α / (α + β) := by
  have hmoment := integral_pow_betaMeasure hα hβ 1
  simp only [pow_one, Nat.cast_one] at hmoment
  rw [hmoment, Real.Gamma_add_one hα.ne', Real.Gamma_add_one (add_pos hα hβ).ne']
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα),
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos hα hβ)), ne_of_gt (add_pos hα hβ)]

/-- The variance of a beta distribution with positive shape parameters. -/
@[simp]
theorem variance_id_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    variance id (betaMeasure α β) =
      α * β / ((α + β) ^ 2 * (α + β + 1)) := by
  let _ : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  have hmem : MemLp id 2 (betaMeasure α β) :=
    memLp_of_bounded (ae_mem_Icc_betaMeasure α β) measurable_id.aestronglyMeasurable 2
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq, integral_pow_betaMeasure hα hβ 2,
    integral_id_betaMeasure hα hβ]
  norm_num only [Nat.cast_ofNat]
  rw [Gamma_add_two hα, Gamma_add_two (add_pos hα hβ)]
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα),
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos hα hβ)),
    ne_of_gt (add_pos hα hβ)]
  ring_nf

/-- Every exponential moment of a beta distribution with positive shape parameters exists. -/
@[simp]
theorem integrableExpSet_id_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    integrableExpSet id (betaMeasure α β) = Set.univ := by
  let _ : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  ext t
  simp only [Set.mem_univ, iff_true, integrableExpSet, Set.mem_ofPred_eq, id_eq]
  exact integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable
    (ae_mem_Icc_betaMeasure α β)

end TauCeti
