/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import TauCeti.Analysis.Analytic.Binomial
public import TauCeti.Probability.GeneratingFunction
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The negative-binomial distribution

This file begins the negative-binomial family from the standard-distributions roadmap.  The law
counts failures before the `r`th success, with real shape `r` and success probability `p`.  Its
native mass is the Gamma-expression
`Γ(k + r) / (k! Γ(r)) * p^r * (1 - p)^k`.

The definition is totalized explicitly: the positive family is used for `0 < r` and `0 < p ≤ 1`,
the boundary `r = 0` is a Dirac mass at zero, and every other parameter value gives the zero
measure.  The file supplies the normalized measure, its native singleton interface, and the exact
integrability domain and closed form of its probability-generating function.

The normalization uses Mathlib's real binomial power series, after identifying its coefficients
with the Gamma quotient.  The distributional convention follows Johnson, Kemp, and Kotz,
*Univariate Discrete Distributions*, 3rd ed., Chapter 6.

Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, **Negative binomial**.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

/-- The real coefficient in the negative-binomial mass at `k`. -/
def negativeBinomialWeightReal (r p : ℝ) (k : ℕ) : ℝ :=
  if r = 0 then if k = 0 then 1 else 0
  else Real.Gamma (k + r) / (k.factorial * Real.Gamma r) * Real.rpow p r * (1 - p) ^ k

/-- The `ℝ≥0∞`-valued negative-binomial mass at `k`. -/
def negativeBinomialWeight (r p : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (negativeBinomialWeightReal r p k)

/-- The negative-binomial law with real shape `r` and success probability `p`.

For `0 < r` and `0 < p ≤ 1` this is the weighted Dirac sum with the usual Gamma masses.  The
boundary shape `r = 0` is the Dirac law at zero; all remaining parameters are totalized to zero. -/
def negativeBinomialMeasure (r p : ℝ) : Measure ℕ :=
  if 0 < r ∧ 0 < p ∧ p ≤ 1 then
    Measure.sum (fun k => negativeBinomialWeight r p k • Measure.dirac k)
  else if r = 0 ∧ 0 < p ∧ p ≤ 1 then
    Measure.dirac 0
  else 0

/-- In the valid parameter range, the measure is its weighted Dirac sum, including `r = 0`. -/
theorem negativeBinomialMeasure_eq_sum_dirac {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    negativeBinomialMeasure r p =
      Measure.sum (fun k => negativeBinomialWeight r p k • Measure.dirac k) := by
  rcases hr.eq_or_lt with rfl | hr
  · have hmeasure : negativeBinomialMeasure 0 p = Measure.dirac 0 := by
      simp [negativeBinomialMeasure, hp, hp1]
    rw [hmeasure, ← Measure.sum_smul_dirac (Measure.dirac 0)]
    congr 1
    funext k
    by_cases hk : k = 0
    · subst k
      simp [negativeBinomialWeight, negativeBinomialWeightReal]
    · simp [negativeBinomialWeight, negativeBinomialWeightReal, hk]
  · simp [negativeBinomialMeasure, hr, hp, hp1]

/-- Outside the probability parameter range, the measure is explicitly totalized to zero. -/
@[simp]
theorem negativeBinomialMeasure_eq_zero_of_invalid {r p : ℝ}
    (h : ¬ (0 ≤ r ∧ 0 < p ∧ p ≤ 1)) : negativeBinomialMeasure r p = 0 := by
  rw [negativeBinomialMeasure]
  split_ifs with h₁ h₂
  · exact (h ⟨h₁.1.le, h₁.2⟩).elim
  · exact (h ⟨h₂.1.ge, h₂.2⟩).elim
  · rfl

/-- The boundary shape `r = 0` is the Dirac law at zero in the valid probability range. -/
@[simp]
theorem negativeBinomialMeasure_zero {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    negativeBinomialMeasure 0 p = Measure.dirac 0 := by
  simp [negativeBinomialMeasure, hp, hp1]

/-- At nonzero shape, the real negative-binomial weight has its defining Gamma-quotient form. -/
@[simp]
theorem negativeBinomialWeightReal_eq_gamma (hr : r ≠ 0) (k : ℕ) :
    negativeBinomialWeightReal r p k =
      Real.Gamma (k + r) / (k.factorial * Real.Gamma r) * Real.rpow p r * (1 - p) ^ k := by
  rw [negativeBinomialWeightReal, ite_eq_right hr]

private theorem gamma_ratio_eq_multichoose (hr : 0 < r) (k : ℕ) :
    Real.Gamma (k + r) / (k.factorial * Real.Gamma r) = Ring.multichoose r k := by
  have hpoch : ∀ n : ℕ,
      (ascPochhammer ℕ n).smeval r = Real.Gamma (n + r) / Real.Gamma r := by
    intro n
    rw [Polynomial.ascPochhammer_smeval_eq_eval]
    have hz : ∀ m : ℕ, (r : ℂ) ≠ -m := by
      intro m hm
      have : r = -(m : ℝ) := by exact_mod_cast congrArg Complex.re hm
      linarith [hr]
    have h := Complex.Gamma_add_nat_div_Gamma_eq (n := n) (r : ℂ) hz
    have hpoly : (ascPochhammer ℂ n).eval (r : ℂ) =
        Complex.ofRealHom ((ascPochhammer ℝ n).eval r) := by
      rw [ascPochhammer_eval₂ (S := ℝ) (T := ℂ) Complex.ofRealHom]
      exact Polynomial.eval₂_at_apply Complex.ofRealHom r
    have hcomplex : ((Real.Gamma (n + r) / Real.Gamma r : ℝ) : ℂ) =
        (ascPochhammer ℂ n).eval (r : ℂ) := by
      have harg : (r : ℂ) + n = ((n + r : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h.symm, harg]
      simp only [Complex.Gamma_ofReal, Complex.ofReal_div]
    exact Complex.ofReal_inj.mp (hcomplex.trans hpoly).symm
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r k
  rw [nsmul_eq_mul, hpoch] at h
  calc
    Real.Gamma (k + r) / (k.factorial * Real.Gamma r) =
        (Real.Gamma (k + r) / Real.Gamma r) / k.factorial := by ring
    _ = ((k.factorial : ℝ) * Ring.multichoose r k) / k.factorial := by rw [← h]
    _ = Ring.multichoose r k := by field_simp

/-- The real negative-binomial mass in its multichoose coefficient form. -/
theorem negativeBinomialWeightReal_eq_coeff (hr : 0 < r) (k : ℕ) :
    negativeBinomialWeightReal r p k =
      (Ring.multichoose r k : ℝ) * Real.rpow p r * (1 - p) ^ k := by
  rw [negativeBinomialWeightReal_eq_gamma hr.ne' k, gamma_ratio_eq_multichoose hr k]

private theorem negativeBinomialWeightReal_nonneg (hr : 0 ≤ r) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) : 0 ≤ negativeBinomialWeightReal r p k := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [negativeBinomialWeightReal]
    split_ifs <;> norm_num
  rcases hp.eq_or_lt with rfl | hp
  · simp [negativeBinomialWeightReal, hr.ne', Real.zero_rpow hr.ne']
  rw [negativeBinomialWeightReal_eq_coeff hr k]
  have hcoeff : 0 ≤ (Ring.multichoose r k : ℝ) := by
    rw [← gamma_ratio_eq_multichoose hr k]
    exact div_nonneg (Real.Gamma_pos_of_pos (by positivity)).le
      (mul_nonneg (by positivity) (Real.Gamma_pos_of_pos hr).le)
  exact mul_nonneg (mul_nonneg hcoeff (Real.rpow_pos_of_pos hp r).le)
    (pow_nonneg (by linarith) k)

/-- The real-valued mass agrees with the `toReal` of the nonnegative mass, including boundaries. -/
theorem negativeBinomialWeight_toReal (hr : 0 ≤ r) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    (negativeBinomialWeight r p k).toReal =
      negativeBinomialWeightReal r p k := by
  rw [negativeBinomialWeight, ENNReal.toReal_ofReal]
  exact negativeBinomialWeightReal_nonneg hr hp hp1 k

private theorem hasSum_negativeBinomialWeightReal_mul_pow (hr : 0 < r) (hp : 0 < p)
    {t : ℝ} (ht : |(1 - p) * t| < 1) :
    HasSum (fun k => negativeBinomialWeightReal r p k * t ^ k)
      (Real.rpow (p / (1 - (1 - p) * t)) r) := by
  have hsum := hasSum_multichoose_mul_geometric_of_abs_lt_one (r := r) ht
  have hsum' := hsum.mul_right (Real.rpow p r)
  have hweight (k : ℕ) :
      negativeBinomialWeightReal r p k * t ^ k =
        (Ring.multichoose r k : ℝ) * ((1 - p) * t) ^ k * Real.rpow p r := by
    rw [negativeBinomialWeightReal_eq_coeff hr k, mul_pow]
    ring
  have hden : 0 ≤ 1 - (1 - p) * t := by
    linarith [le_abs_self ((1 - p) * t)]
  -- Normalize the real-power notation inherited from the analytic-series theorem.
  have hden_rpow : (1 - (1 - p) * t) ^ r =
      Real.rpow (1 - (1 - p) * t) r := rfl
  rw [hden_rpow] at hsum'
  have hvalue : 1 / Real.rpow (1 - (1 - p) * t) r * Real.rpow p r =
      Real.rpow (p / (1 - (1 - p) * t)) r := by
    calc
      1 / Real.rpow (1 - (1 - p) * t) r * Real.rpow p r =
          Real.rpow p r / Real.rpow (1 - (1 - p) * t) r := by
            rw [one_div, div_eq_mul_inv, mul_comm]
      _ = Real.rpow (p / (1 - (1 - p) * t)) r :=
        (Real.div_rpow hp.le hden r).symm
  rw [hvalue] at hsum'
  exact HasSum.congr_fun hsum' hweight

private theorem hasSum_negativeBinomialWeightReal (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun k => negativeBinomialWeightReal r p k) 1 := by
  have ht : |(1 - p) * (1 : ℝ)| < 1 := by
    rw [mul_one, abs_of_nonneg (by linarith)]
    linarith
  simpa [hp.ne'] using (hasSum_negativeBinomialWeightReal_mul_pow hr hp ht)

/-- The negative-binomial measure is a probability measure in its classical parameter range. -/
theorem isProbabilityMeasure_negativeBinomialMeasure (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (negativeBinomialMeasure r p) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeBinomialMeasure_zero hp hp1]
    infer_instance
  · rw [negativeBinomialMeasure_eq_sum_dirac hr.le hp hp1]
    apply (hasSum_negativeBinomialWeightReal hr hp hp1).isProbabilityMeasure_sum_dirac
    intro k
    exact negativeBinomialWeightReal_nonneg hr.le hp.le hp1 k

/-- The singleton mass of the negative-binomial law in its valid parameter range. -/
@[simp]
theorem negativeBinomialMeasure_singleton {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1)
    (k : ℕ) : negativeBinomialMeasure r p {k} = negativeBinomialWeight r p k := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeBinomialMeasure_zero hp hp1]
    by_cases hk : k = 0
    · subst k
      simp [negativeBinomialWeight, negativeBinomialWeightReal]
    · simp [negativeBinomialWeight, negativeBinomialWeightReal, hk]
  · rw [negativeBinomialMeasure_eq_sum_dirac hr.le hp hp1]
    exact Measure.sum_smul_dirac_singleton

/-- The real singleton mass of the negative-binomial law in its valid parameter range. -/
theorem negativeBinomialMeasure_real_singleton {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1)
    (k : ℕ) :
    (negativeBinomialMeasure r p).real {k} = negativeBinomialWeightReal r p k := by
  rw [measureReal_def, negativeBinomialMeasure_singleton hr hp hp1,
    negativeBinomialWeight_toReal hr hp.le hp1]

/-- For positive shape and valid success probability, the negative-binomial
probability-generating-function integrand is integrable exactly inside its disk of convergence.
Thus it is non-integrable both on and beyond the boundary. -/
theorem integrable_pow_negativeBinomialMeasure_iff {r p : ℝ} (hr : 0 < r)
    (hp : 0 < p) (hp1 : p ≤ 1) (t : ℝ) :
    Integrable (fun k : ℕ => t ^ k) (negativeBinomialMeasure r p) ↔
      |(1 - p) * t| < 1 := by
  rw [negativeBinomialMeasure_eq_sum_dirac hr.le hp hp1,
    integrable_sum_dirac_iff (by simp [negativeBinomialWeight])]
  simp_rw [negativeBinomialWeight_toReal hr.le hp.le hp1, Real.norm_eq_abs, abs_pow]
  have hp_rpow : 0 < Real.rpow p r := Real.rpow_pos_of_pos hp r
  have hfun : (fun k : ℕ => negativeBinomialWeightReal r p k * |t| ^ k) =
      (fun k : ℕ => Real.rpow p r *
        ((Ring.multichoose r k : ℝ) * |(1 - p) * t| ^ k)) := by
    funext k
    rw [negativeBinomialWeightReal_eq_coeff hr k, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ 1 - p), mul_pow]
    ring
  rw [hfun, summable_mul_left_iff hp_rpow.ne']
  simpa [Real.norm_eq_abs] using
    (summable_multichoose_mul_geometric_iff_norm_lt_one
      (𝕂 := ℝ) (q := |(1 - p) * t|) hr)

/-- The probability-generating function of a negative-binomial law with positive shape, on its
exact integrability domain. -/
theorem pgf_negativeBinomialMeasure {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1)
    {t : ℝ} (ht : |(1 - p) * t| < 1) :
    pgf id (negativeBinomialMeasure r p) t =
      Real.rpow (p / (1 - (1 - p) * t)) r := by
  rw [pgf_def, negativeBinomialMeasure_eq_sum_dirac hr.le hp hp1,
    integral_sum_dirac (by simp [negativeBinomialWeight])]
  simp only [id_eq, smul_eq_mul]
  rw [← (hasSum_negativeBinomialWeightReal_mul_pow hr hp ht).tsum_eq]
  congr with k
  rw [negativeBinomialWeight_toReal hr.le hp.le hp1]

/-- At shape zero, the negative-binomial PGF is one in the valid probability range and zero
outside it, in accordance with the totalization of `negativeBinomialMeasure`. -/
@[simp]
theorem pgf_negativeBinomialMeasure_zero (p t : ℝ) :
    pgf id (negativeBinomialMeasure 0 p) t = if 0 < p ∧ p ≤ 1 then 1 else 0 := by
  by_cases h : 0 < p ∧ p ≤ 1
  · rw [ite_eq_left h, negativeBinomialMeasure_zero h.1 h.2, pgf_def]
    simp
  · rw [ite_eq_right h]
    have hz : negativeBinomialMeasure 0 p = 0 := by
      apply negativeBinomialMeasure_eq_zero_of_invalid
      simpa using h
    rw [hz, pgf_def]
    simp

end Probability

end TauCeti
