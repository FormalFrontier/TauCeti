/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.Probability.Distributions.StudentT.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
import TauCeti.Analysis.Calculus.RealCharts
import TauCeti.Probability.Distributions.StudentT.WeightedIntegral
import TauCeti.Analysis.SpecialFunctions.Beta
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Moments of Student's t law

This file proves the mean, variance, polynomial moment thresholds and exponential moment domain of
the Student t distribution defined in `TauCeti/Probability/Distributions/StudentT/Basic.lean`. The
cumulative distribution function is computed in
`TauCeti/Probability/Distributions/StudentT/Cdf.lean`. The density is even, and on the positive
half-line the substitution `w = x ^ 2 / ν` turns every weighted integral into Euler's second beta
integral
`∫ w ^ (a - 1) * (1 + w) ^ (-(a + b)) = Β(a, b)`, so the weighted density is integrable there
exactly for `-1 < q < ν`; the exponential-moment statements read off that sharp threshold.

## Main results

* `integrable_id_studentTMeasure_iff` and `integral_id_studentTMeasure` — within the nondegenerate
  family the mean exists exactly when `1 < ν`, while its Bochner integral is zero for every
  parameter;
* `integrable_sq_studentTMeasure_iff`, `integral_sq_studentTMeasure` and
  `variance_id_studentTMeasure` — the second moment exists exactly when `2 < ν`, and then both it
  and the variance equal `ν / (ν - 2)`;
* `integrable_exp_mul_id_studentTMeasure_iff` — `exp (t · x)` is integrable exactly at `t = 0`;
* `integrableExpSet_id_studentTMeasure` — the exponential-moment domain is the singleton `{0}`,
  together with the matching non-integrability statement for every nonzero rate.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 28.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Real

namespace TauCeti

namespace Probability

variable {ν q x t : ℝ}

/-! ### Polynomial moments -/

private lemma studentTKernel_id_factor (hν : 0 < ν) (x : ℝ) :
    (x / √(1 + x ^ 2 / ν)) * (1 + x ^ 2 / ν) ^ (-(ν / 2)) =
      x * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by
  have hbase : 0 < 1 + x ^ 2 / ν := by positivity
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hbase.le, mul_assoc,
    ← Real.rpow_add hbase]
  congr 2
  ring

private lemma integrable_id_mul_studentTKernel (hν : 1 < ν) :
    Integrable (fun x : ℝ =>
      x * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
  have hνpos : 0 < ν := lt_trans zero_lt_one hν
  have hkernel : Integrable (fun x : ℝ => (1 + x ^ 2 / ν) ^ (-(ν / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  have hbounded : ∀ x : ℝ, ‖x / √(1 + x ^ 2 / ν)‖ ≤ √ν := by
    intro x
    have hbase : 0 < 1 + x ^ 2 / ν := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.sqrt_pos.mpr hbase),
      div_le_iff₀ (Real.sqrt_pos.mpr hbase)]
    have hsq : |x| ^ 2 ≤ (√ν * √(1 + x ^ 2 / ν)) ^ 2 := by
      rw [sq_abs, mul_pow, Real.sq_sqrt hνpos.le, Real.sq_sqrt hbase.le]
      have hmul : ν * (1 + x ^ 2 / ν) = ν + x ^ 2 := by field_simp
      rw [hmul]
      linarith
    have hprod_nonneg : 0 ≤ √ν * √(1 + x ^ 2 / ν) :=
      mul_nonneg (Real.sqrt_nonneg ν) (Real.sqrt_nonneg (1 + x ^ 2 / ν))
    nlinarith [abs_nonneg x]
  have hproduct : Integrable (fun x : ℝ =>
      (x / √(1 + x ^ 2 / ν)) * (1 + x ^ 2 / ν) ^ (-(ν / 2))) :=
    hkernel.bdd_mul (measurable_id.div
      (Real.continuous_sqrt.measurable.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ hbounded)
  exact hproduct.congr (ae_of_all _ fun x => studentTKernel_id_factor hνpos x)

private theorem integrable_id_studentTMeasure_of_one_lt (hν : 1 < ν) :
    Integrable id (studentTMeasure ν) := by
  have hνpos : 0 < ν := lt_trans zero_lt_one hν
  rw [studentTMeasure_def, integrable_withDensity_iff (measurable_studentTPDF ν)
    (ae_of_all _ fun x => studentTPDF_lt_top ν x)]
  simp_rw [id_eq, toReal_studentTPDF, studentTPDFReal_of_pos hνpos]
  have h := (integrable_id_mul_studentTKernel hν).const_mul
    (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)))
  exact h.congr (ae_of_all _ fun x => by ring)

private theorem studentTPDFReal_tail_lower_bound (hν : 0 < ν) (q : ℕ)
    (hνq : ν ≤ (q : ℝ)) :
    ∀ᶠ x : ℝ in atTop,
      (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2))) *
          (1 + ν⁻¹) ^ (-(((q : ℝ) + 1) / 2)) * x⁻¹ ≤
        x ^ q * studentTPDFReal ν x := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  -- On the right tail, compare the kernel base with a constant multiple of `x²`, then use
  -- `ν ≤ q` to compare the two negative exponents.
  have hbase_pos : 0 < 1 + x ^ 2 / ν := by positivity
  have hbase_one : 1 ≤ 1 + x ^ 2 / ν :=
    le_add_of_nonneg_right (div_nonneg (sq_nonneg x) hν.le)
  have hconst_pos : 0 < 1 + ν⁻¹ := by positivity
  have hdensity_pos :
      0 < Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)) :=
    studentT_const_pos hν
  have hbase_le : 1 + x ^ 2 / ν ≤ (1 + ν⁻¹) * x ^ 2 := by
    have hx_sq : 1 ≤ x ^ 2 := (one_le_sq_iff₀ hx0.le).2 hx
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg (zero_le_one.trans hx_sq) (inv_nonneg.mpr hν.le)]
  have hexp : -(((q : ℝ) + 1) / 2) ≤ -((ν + 1) / 2) := by
    norm_num at hνq ⊢
    linarith
  have hpow₁ : (1 + x ^ 2 / ν) ^ (-(((q : ℝ) + 1) / 2)) ≤
      (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hbase_one hexp
  have hpow₂ : ((1 + ν⁻¹) * x ^ 2) ^ (-(((q : ℝ) + 1) / 2)) ≤
      (1 + x ^ 2 / ν) ^ (-(((q : ℝ) + 1) / 2)) :=
    Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by
      have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
      linarith)
  -- Splitting the comparison kernel exposes exactly `x ^ q * x ^ (-(q + 1)) = x⁻¹`.
  have hsplit : ((1 + ν⁻¹) * x ^ 2) ^ (-(((q : ℝ) + 1) / 2)) =
      (1 + ν⁻¹) ^ (-(((q : ℝ) + 1) / 2)) * x ^ (-((q : ℝ) + 1)) := by
    rw [Real.mul_rpow hconst_pos.le (sq_nonneg x), ← Real.rpow_two x,
      ← Real.rpow_mul hx0.le]
    congr 2
    ring
  have hxpow : x ^ (q : ℝ) * x ^ (-((q : ℝ) + 1)) = x⁻¹ := by
    rw [← Real.rpow_add hx0]
    have hexponent : (q : ℝ) + -((q : ℝ) + 1) = -1 := by ring
    rw [hexponent, Real.rpow_neg_one]
  rw [studentTPDFReal_of_pos hν]
  calc
    (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2))) *
          (1 + ν⁻¹) ^ (-(((q : ℝ) + 1) / 2)) * x⁻¹ =
        (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2))) *
          (x ^ q * ((1 + ν⁻¹) * x ^ 2) ^ (-(((q : ℝ) + 1) / 2))) := by
            rw [hsplit, ← Real.rpow_natCast x q, ← hxpow]
            ring
    _ ≤ (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2))) *
          (x ^ q * (1 + x ^ 2 / ν) ^ (-(((q : ℝ) + 1) / 2))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hpow₂ (pow_nonneg hx0.le q)) hdensity_pos.le
    _ ≤ x ^ q *
          (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)) *
            (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
            calc
              _ ≤ (Real.Gamma ((ν + 1) / 2) /
                    (√(ν * π) * Real.Gamma (ν / 2))) *
                  (x ^ q * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hpow₁ (pow_nonneg hx0.le q))
                  hdensity_pos.le
              _ = _ := by ring
    _ = _ := by ring

private theorem not_integrable_pow_studentTMeasure (hν : 0 < ν) (q : ℕ)
    (hνq : ν ≤ (q : ℝ)) :
    ¬ Integrable (fun x : ℝ => x ^ q) (studentTMeasure ν) := by
  intro hint
  rw [studentTMeasure_def, integrable_withDensity_iff (measurable_studentTPDF ν)
    (ae_of_all _ fun x => studentTPDF_lt_top ν x)] at hint
  simp_rw [toReal_studentTPDF] at hint
  let c : ℝ :=
    (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2))) *
      (1 + ν⁻¹) ^ (-(((q : ℝ) + 1) / 2))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbound : ∀ᶠ x : ℝ in atTop,
      c * x⁻¹ ≤ x ^ q * studentTPDFReal ν x := by
    simpa only [c] using studentTPDFReal_tail_lower_bound hν q hνq
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    (hbound.and (eventually_ge_atTop (1 : ℝ)))
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioi a) volume := by
    refine Integrable.mono' (hint.const_mul c⁻¹).integrableOn (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rcases ha x hx.le with ⟨hpdf, hx1⟩
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    calc
      ‖x⁻¹‖ = x⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
      _ = c⁻¹ * (c * x⁻¹) := by field_simp
      _ ≤ c⁻¹ * (x ^ q * studentTPDFReal ν x) :=
        mul_le_mul_of_nonneg_left hpdf (inv_nonneg.mpr hc.le)
  exact not_integrableOn_Ioi_inv hinv

/-- The identity is integrable under a nondegenerate Student t law exactly when the number of
degrees of freedom exceeds one. -/
@[simp]
theorem integrable_id_studentTMeasure_iff (hν : 0 < ν) :
    Integrable id (studentTMeasure ν) ↔ 1 < ν := by
  constructor
  · intro hint
    by_contra h
    have hnot := not_integrable_pow_studentTMeasure hν 1 (by
      simpa using (not_lt.mp h : ν ≤ 1))
    have hint' : Integrable (fun x : ℝ => x) (studentTMeasure ν) := by
      refine hint.congr (ae_of_all _ fun x => ?_)
      rfl
    apply hnot
    simpa only [pow_one] using hint'
  · exact integrable_id_studentTMeasure_of_one_lt

/-- The Bochner integral of the identity under a Student t measure is zero for every parameter,
including by convention when the identity is not integrable. -/
@[simp]
theorem integral_id_studentTMeasure (ν : ℝ) :
    ∫ x, x ∂studentTMeasure ν = 0 := by
  by_cases hint : Integrable (fun x : ℝ => x) (studentTMeasure ν)
  · have hpres : MeasurePreserving (fun x : ℝ => -x)
        (studentTMeasure ν) (studentTMeasure ν) :=
      ⟨measurable_neg, studentTMeasure_map_neg ν⟩
    have hrefl : ∫ x, -x ∂studentTMeasure ν = ∫ x, x ∂studentTMeasure ν := by
      simpa only [Function.comp_apply, id_eq] using
        hpres.integral_comp (Homeomorph.neg ℝ).measurableEmbedding id
    have hneg : Integrable (fun x : ℝ => -x) (studentTMeasure ν) := hint.neg
    have hsum : (∫ x, x ∂studentTMeasure ν) + ∫ x, -x ∂studentTMeasure ν = 0 := by
      rw [← integral_add hint hneg]
      simp
    linarith
  · exact integral_undef hint

private lemma studentTKernel_sq (hν : 0 < ν) (x : ℝ) :
    x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) =
      ν * ((1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) -
        (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
  have hbase : 0 < 1 + x ^ 2 / ν := by positivity
  have hshift :
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) =
        (1 + x ^ 2 / ν) * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by
    calc
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) =
          (1 + x ^ 2 / ν) ^ (1 + -((ν + 1) / 2)) := by
        apply congrArg (fun t : ℝ => (1 + x ^ 2 / ν) ^ t)
        ring
      _ = (1 + x ^ 2 / ν) ^ 1 *
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := Real.rpow_add hbase _ _
      _ = (1 + x ^ 2 / ν) *
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by rw [Real.rpow_one]
  rw [hshift]
  field_simp
  ring

private lemma integrable_sq_mul_studentTKernel (hν : 2 < ν) :
    Integrable (fun x : ℝ =>
      x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
  have hνpos : 0 < ν := lt_trans zero_lt_two hν
  have hshift : Integrable (fun x : ℝ =>
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  have hbase : Integrable (fun x : ℝ =>
      (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  exact ((hshift.sub hbase).const_mul ν).congr
    (ae_of_all _ fun x => (studentTKernel_sq hνpos x).symm)

private theorem integrable_sq_studentTMeasure_of_two_lt (hν : 2 < ν) :
    Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) := by
  have hνpos : 0 < ν := lt_trans zero_lt_two hν
  rw [studentTMeasure_def, integrable_withDensity_iff (measurable_studentTPDF ν)
    (ae_of_all _ fun x => studentTPDF_lt_top ν x)]
  simp_rw [toReal_studentTPDF, studentTPDFReal_of_pos hνpos]
  have h := (integrable_sq_mul_studentTKernel hν).const_mul
    (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)))
  exact h.congr (ae_of_all _ fun x => by ring)

private lemma beta_sub_beta_add_one (hν : 2 < ν) :
    beta (1 / 2) ((ν - 2) / 2) - beta (1 / 2) (ν / 2) =
      beta (3 / 2) ((ν - 2) / 2) := by
  let b := (ν - 2) / 2
  have hb : b ≠ 0 := by
    dsimp [b]
    linarith
  have hsum : b + 1 / 2 ≠ 0 := by
    dsimp [b]
    linarith
  have hright : beta (1 / 2) (b + 1) =
      b / (b + 1 / 2) * beta (1 / 2) b := by
    rw [beta_comm (1 / 2) (b + 1), beta_add_one_left hb hsum,
      beta_comm b (1 / 2)]
  have hleft : beta (1 / 2 + 1) b =
      (1 / 2) / (1 / 2 + b) * beta (1 / 2) b :=
    beta_add_one_left (by norm_num) (by simpa [add_comm] using hsum)
  have hνdiv : ν / 2 = b + 1 := by
    dsimp [b]
    ring
  have hthree : (3 : ℝ) / 2 = 1 / 2 + 1 := by ring
  rw [hνdiv, hthree, hright, hleft]
  have hcoeff : 1 - b / (b + 1 / 2) = (1 / 2) / (1 / 2 + b) := by
    have hsum' : 1 / 2 + b ≠ 0 := by simpa [add_comm] using hsum
    have hbhalf : b + 1 / 2 = 1 / 2 + b := by ring
    rw [hbhalf]
    apply (eq_div_iff hsum').2
    rw [sub_mul, one_mul, div_mul_cancel₀ b hsum']
    ring
  calc
    beta (1 / 2) b - b / (b + 1 / 2) * beta (1 / 2) b =
        (1 - b / (b + 1 / 2)) * beta (1 / 2) b := by ring
    _ = (1 / 2) / (1 / 2 + b) * beta (1 / 2) b := by rw [hcoeff]

private lemma integral_sq_mul_studentTKernel (hν : 2 < ν) :
    ∫ x : ℝ, x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) =
      ν * √ν * beta (3 / 2) ((ν - 2) / 2) := by
  have hνpos : 0 < ν := lt_trans zero_lt_two hν
  have hshift : Integrable (fun x : ℝ =>
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  have hbase : Integrable (fun x : ℝ =>
      (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  have hminus : (ν - 1) / 2 - 1 / 2 = (ν - 2) / 2 := by ring
  have hplus : (ν + 1) / 2 - 1 / 2 = ν / 2 := by ring
  calc
    ∫ x : ℝ, x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) =
        ∫ x : ℝ, ν * ((1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) -
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
      exact integral_congr_ae (ae_of_all _ fun x => studentTKernel_sq hνpos x)
    _ = ν * ((∫ x : ℝ, (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2))) -
          ∫ x : ℝ, (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
      rw [integral_const_mul, integral_sub hshift hbase]
    _ = ν * (√ν * beta (1 / 2) ((ν - 1) / 2 - 1 / 2) -
          √ν * beta (1 / 2) ((ν + 1) / 2 - 1 / 2)) := by
      rw [integral_one_add_sq_div_rpow hνpos (by linarith),
        integral_one_add_sq_div_rpow hνpos (by linarith)]
    _ = ν * √ν * beta (3 / 2) ((ν - 2) / 2) := by
      rw [hminus, hplus, ← mul_sub, beta_sub_beta_add_one hν]
      ring

/-- The second raw moment of a Student t law is `ν / (ν - 2)` when `2 < ν`. -/
@[simp]
theorem integral_sq_studentTMeasure (hν : 2 < ν) :
    ∫ x, x ^ 2 ∂studentTMeasure ν = ν / (ν - 2) := by
  have hνpos : 0 < ν := lt_trans zero_lt_two hν
  have hbpos : 0 < (ν - 2) / 2 := by linarith
  have hGν : Real.Gamma (ν / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGb : Real.Gamma ((ν - 2) / 2) ≠ 0 := (Real.Gamma_pos_of_pos hbpos).ne'
  have hGs : Real.Gamma ((ν + 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hsqrtν : √ν ≠ 0 := (Real.sqrt_pos.mpr hνpos).ne'
  have hsqrtπ : √π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsub : ν - 2 ≠ 0 := by linarith
  have hthree : (3 : ℝ) / 2 = 1 / 2 + 1 := by ring
  have hgammaSum : (1 : ℝ) / 2 + 1 + (ν - 2) / 2 = (ν + 1) / 2 := by ring
  have hνhalf : ν / 2 = (ν - 2) / 2 + 1 := by ring
  rw [studentTMeasure_def, integral_withDensity_eq_integral_toReal_smul
    (measurable_studentTPDF ν) (ae_of_all _ fun x => studentTPDF_lt_top ν x)]
  simp_rw [toReal_studentTPDF, smul_eq_mul, studentTPDFReal_of_pos hνpos]
  calc
    ∫ x : ℝ, (Real.Gamma ((ν + 1) / 2) /
          (√(ν * π) * Real.Gamma (ν / 2)) *
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) * x ^ 2 =
        Real.Gamma ((ν + 1) / 2) /
          (√(ν * π) * Real.Gamma (ν / 2)) *
          ∫ x : ℝ, x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = Real.Gamma ((ν + 1) / 2) /
          (√(ν * π) * Real.Gamma (ν / 2)) *
          (ν * √ν * beta (3 / 2) ((ν - 2) / 2)) := by
      rw [integral_sq_mul_studentTKernel hν]
    _ = ν / (ν - 2) := by
      rw [ProbabilityTheory.beta, hthree,
        Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0),
        Real.Gamma_one_half_eq, hgammaSum, hνhalf,
        Real.Gamma_add_one (ne_of_gt hbpos), Real.sqrt_mul hνpos.le]
      field_simp

/-- Squaring is integrable under a nondegenerate Student t law exactly when the number of degrees
of freedom exceeds two. -/
@[simp]
theorem integrable_sq_studentTMeasure_iff (hν : 0 < ν) :
    Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) ↔ 2 < ν := by
  constructor
  · intro hint
    by_contra h
    exact not_integrable_pow_studentTMeasure hν 2 (by
      simpa using (not_lt.mp h : ν ≤ 2)) hint
  · exact integrable_sq_studentTMeasure_of_two_lt

/-- At or below two degrees of freedom, the second raw moment of a nondegenerate Student t law
diverges. -/
theorem not_integrable_sq_studentTMeasure (hν : 0 < ν) (hν2 : ν ≤ 2) :
    ¬ Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) := by
  rw [integrable_sq_studentTMeasure_iff hν]
  exact not_lt.mpr hν2

/-- The variance of a Student t law is `ν / (ν - 2)` when `2 < ν`. -/
@[simp]
theorem variance_id_studentTMeasure (hν : 2 < ν) :
    variance id (studentTMeasure ν) = ν / (ν - 2) := by
  have _ : IsProbabilityMeasure (studentTMeasure ν) :=
    isProbabilityMeasure_studentTMeasure (lt_trans zero_lt_two hν)
  have hmem : MemLp id 2 (studentTMeasure ν) :=
    (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).2
      (by simpa using integrable_sq_studentTMeasure_of_two_lt hν)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_studentTMeasure hν, integral_id_studentTMeasure]
  ring

/-- On the right tail the Student-t beta kernel dominates a constant multiple of the
corresponding pure power. This is the comparison that carries the non-integrability at infinity. -/
private lemma eventually_const_mul_rpow_le_studentTBetaKernel (hν : 0 < ν) {q : ℝ} :
    ∀ᶠ w in atTop,
      (2 : ℝ) ^ (-((ν + 1) / 2)) * w ^ ((q - ν - 2) / 2) ≤ studentTBetaKernel ν q w := by
  set s := (ν + 1) / 2
  set e := (q - ν - 2) / 2 with he
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with w hw
  -- For large `w`, compare `(1 + w) ^ (-s)` with `(2w) ^ (-s)`.
  have hw0 : 0 < w := by linarith
  have hle : 1 + w ≤ 2 * w := by
    have h : 1 ≤ w := hw
    linarith
  have hpos1 : 0 < 1 + w := by linarith
  have hpos2 : 0 < 2 * w := by linarith
  have hs_pos : 0 < s := by
    dsimp only [s]
    linarith [hν]
  have hp : (1 + w) ^ s ≤ (2 * w) ^ s :=
    Real.rpow_le_rpow hpos1.le hle hs_pos.le
  have hneg1 : (1 + w) ^ (-s) = ((1 + w) ^ s)⁻¹ :=
    Real.rpow_neg hpos1.le s
  have hneg2 : (2 * w) ^ (-s) = ((2 * w) ^ s)⁻¹ :=
    Real.rpow_neg hpos2.le s
  have h : (2 * w) ^ (-s) ≤ (1 + w) ^ (-s) := by
    rw [hneg2, hneg1]
    have hpos : 0 < (1 + w) ^ s := Real.rpow_pos_of_pos hpos1 s
    have h9 : 1 / (2 * w) ^ s ≤ 1 / (1 + w) ^ s :=
      one_div_le_one_div_of_le hpos hp
    simpa [div_eq_mul_inv] using h9
  have h9' : (2 * w) ^ (-s) = (2 : ℝ) ^ (-s) * w ^ (-s) := by
    rw [Real.mul_rpow (by positivity) hw0.le]
  have h12 : w ^ e = w ^ ((q - 1) / 2) * w ^ (-s) := by
    have heq' : (q - 1) / 2 + (-s) = e := by
      dsimp only [e, s]; ring_nf
    have h12' : w ^ ((q - 1) / 2) * w ^ (-s) = w ^ e := by
      rw [← Real.rpow_add hw0 ((q - 1) / 2) (-s), heq']
    exact h12'.symm
  have hgoal :
      (2 : ℝ) ^ (-s) * w ^ e ≤ w ^ ((q - 1) / 2) * (1 + w) ^ (-s) := by
    calc
      (2 : ℝ) ^ (-s) * w ^ e
        = (2 : ℝ) ^ (-s) * (w ^ ((q - 1) / 2) * w ^ (-s)) := by rw [h12]
      _ = w ^ ((q - 1) / 2) * ((2 : ℝ) ^ (-s) * w ^ (-s)) := by ring
      _ = w ^ ((q - 1) / 2) * (2 * w) ^ (-s) := by rw [h9']
      _ ≤ w ^ ((q - 1) / 2) * (1 + w) ^ (-s) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hw0.le _)
  simpa [studentTBetaKernel, s, e] using hgoal

/-- If the tail exponent is at least `-1`, the beta-kernel tail comparison forces divergence. -/
private lemma not_integrableOn_studentTBetaKernel_Ioi_of_le (hν : 0 < ν)
    (hνq : ν ≤ q) : ¬ IntegrableOn (studentTBetaKernel ν q) (Ioi (0 : ℝ)) := by
  intro h
  set s := (ν + 1) / 2
  set e := (q - ν - 2) / 2 with he
  -- The tail comparison transfers integrability to a nonintegrable pure power.
  have he1 : -1 ≤ e := by linarith
  have hbound := eventually_const_mul_rpow_le_studentTBetaKernel (q := q) hν
  have hIoi1 : IntegrableOn (studentTBetaKernel ν q) (Ioi (1 : ℝ)) :=
    h.mono_set fun x hx => mem_Ioi.mpr (by linarith [mem_Ioi.mp hx])
  obtain ⟨a0, ha0⟩ := eventually_atTop.mp hbound
  set a := max a0 1 with ha_def
  have ha : ∀ w : ℝ, a ≤ w → (2 : ℝ) ^ (-s) * w ^ e ≤ studentTBetaKernel ν q w := by
    intro w hw
    exact ha0 w (le_trans (le_max_left a0 1) hw)
  let f : ℝ → ℝ := fun w => (2 : ℝ) ^ (-s) * w ^ e
  have hf_contOn : ContinuousOn f (Icc (1 : ℝ) a) := by
    apply ContinuousOn.mul
    · exact continuous_const.continuousOn
    · intro x hx
      have hx1 : x ≠ 0 := by
        have h2 : 1 ≤ x := hx.1
        linarith
      exact Real.continuousAt_rpow_const x e (Or.inl hx1) |>.continuousWithinAt
  have hbounded : IntegrableOn f (Icc (1 : ℝ) a) :=
    hf_contOn.integrableOn_Icc
  have hbounded' : IntegrableOn f (Ioc (1 : ℝ) a) :=
    hbounded.mono_set Ioc_subset_Icc_self
  have hae : ∀ᵐ w ∂volume.restrict (Ioi a), |f w| ≤ studentTBetaKernel ν q w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hwa : a ≤ w := le_of_lt hw
    have hwpos : 0 < w := by
      have h1 : 1 ≤ a := by simp [ha_def]
      linarith
    have hnonneg : 0 ≤ f w := by
      dsimp only [f]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hwpos.le _)
    have habs : |f w| = f w := abs_of_nonneg hnonneg
    rw [habs]
    exact ha w hwa
  have ha1 : 1 ≤ a := by
    simp [ha_def]
  have hIoi_a : IntegrableOn (studentTBetaKernel ν q) (Ioi a) :=
    hIoi1.mono_set fun x hx => by
      have hxa : a < x := hx
      have h : 1 < x := by linarith [ha1, hxa]
      exact h
  have htail : IntegrableOn f (Ioi a) :=
    hIoi_a.mono' (by fun_prop) hae
  have hconst : IntegrableOn f (Ioi (1 : ℝ)) := by
    have hdisj : Disjoint (Ioc (1 : ℝ) a) (Ioi a) := by
      simp [Set.disjoint_left]
    have hunion : Ioc (1 : ℝ) a ∪ Ioi a = Ioi (1 : ℝ) := by
      ext x; simp [ha_def]
    have : IntegrableOn f (Ioc (1 : ℝ) a ∪ Ioi a) :=
      hbounded'.union htail
    rwa [hunion] at this
  have hc : IsUnit ((2 : ℝ) ^ (-s)) :=
    isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hpow : IntegrableOn (fun w : ℝ => w ^ e) (Ioi (1 : ℝ)) := by
    have h : IntegrableOn (fun w : ℝ => (2 : ℝ) ^ (-s) * w ^ e) (Ioi (1 : ℝ)) := hconst
    have h' : IntegrableOn (fun w : ℝ => w ^ e) (Ioi (1 : ℝ)) := by
      simpa [IntegrableOn, integrable_const_mul_iff hc] using h
    exact h'
  rw [integrableOn_Ioi_rpow_iff one_pos] at hpow
  linarith

/-- The beta kernel is integrable on the positive half-line precisely for `-1 < q < ν`: the
exponent at `0` is `(q - 1) / 2` and the tail exponent is `(q - ν - 2) / 2`. -/
private lemma integrableOn_studentTBetaKernel_Ioi_iff (hν : 0 < ν) (hq : -1 < q) :
    IntegrableOn (studentTBetaKernel ν q) (Ioi (0 : ℝ)) ↔ q < ν := by
  set s := (ν + 1) / 2
  constructor
  · intro h
    by_contra hqν
    exact not_integrableOn_studentTBetaKernel_Ioi_of_le hν (not_lt.mp hqν) h
  · intro hqν
    set ha := (q + 1) / 2
    set hb := (ν - q) / 2 with hb_def
    have ha_pos : 0 < ha := by
      dsimp only [ha]; linarith
    have hb_pos : 0 < hb := by
      dsimp only [hb]; linarith
    have hsum : ha + hb = s := by
      dsimp only [ha, hb, s]; ring
    have h := integrableOn_rpow_mul_one_add_rpow ha_pos hb_pos
    have hkernel : ∀ w : ℝ, studentTBetaKernel ν q w =
        w ^ (ha - 1) * (1 + w) ^ (-(ha + hb)) := by
      intro w
      dsimp only [studentTBetaKernel]
      have h1 : (q - 1) / 2 = ha - 1 := by
        dsimp only [ha]; ring
      have h2 : -((ν + 1) / 2) = -(ha + hb) := by
        dsimp only [ha, hb]; ring
      rw [h1, h2]
    have h3 : IntegrableOn (studentTBetaKernel ν q) (Ioi (0 : ℝ)) := by
      have h4 : EqOn (fun w : ℝ => w ^ (ha - 1) * (1 + w) ^ (-(ha + hb)))
          (studentTBetaKernel ν q) (Ioi (0 : ℝ)) := by
        intro w hw
        exact (hkernel w).symm
      exact h.congr_fun h4 measurableSet_Ioi
    exact h3

/-- The weighted Student t density `studentTPDFReal ν x * x ^ q` is integrable on the positive
half-line exactly for `-1 < q < ν`. -/
private theorem integrableOn_pow_mul_studentTPDFReal_Ioi_iff (hν : 0 < ν) (hq : -1 < q) :
    IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) ↔ q < ν := by
  set C := Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2))
  let g : ℝ → ℝ := fun w => C * ν ^ ((q + 1) / 2) / 2 * studentTBetaKernel ν q w
  have hderiv : ∀ z ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun z : ℝ => z ^ 2 / ν) (2 * z / ν) (Ioi (0 : ℝ)) z :=
    fun z _ => (hasDerivAt_sq_div_const ν z).hasDerivWithinAt
  have hiff : IntegrableOn g (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) := by
    have himg0 : (fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ) = Ioi (0 ^ 2 / ν) :=
      image_sq_div_const_Ioi hν (y := 0) le_rfl
    have himg : (fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
      rw [himg0]
      simp
    have h_g_eq : ∀ z : ℝ, 0 < z → |2 * z / ν| • g (z ^ 2 / ν) =
        studentTPDFReal ν z * z ^ q := by
      intro z hz
      simpa [g] using abs_deriv_smul_studentTPDFReal hν q hz
    have h_g_eq' : EqOn (fun z : ℝ => |2 * z / ν| • g (z ^ 2 / ν))
        (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) := by
      intro z hz
      exact h_g_eq z hz
    have himg1 : IntegrableOn (fun z : ℝ => |2 * z / ν| • g (z ^ 2 / ν)) (Ioi (0 : ℝ)) ↔
        IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) := by
      refine ⟨fun h => h.congr_fun h_g_eq' measurableSet_Ioi,
        fun h => h.congr_fun (fun z hz => (h_g_eq' hz).symm) measurableSet_Ioi⟩
    have hpre : IntegrableOn g ((fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ)) ↔
        IntegrableOn (fun z : ℝ => |2 * z / ν| • g (z ^ 2 / ν)) (Ioi (0 : ℝ)) :=
      integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
        (injOn_sq_div_const_Ioi hν.ne') g
    rw [himg] at hpre
    exact hpre.trans himg1
  have hC_ne : C ≠ 0 := (studentT_const_pos hν).ne'
  have hc : IsUnit (C * ν ^ ((q + 1) / 2) / 2) := isUnit_iff_ne_zero.mpr <|
    div_ne_zero (mul_ne_zero hC_ne (Real.rpow_pos_of_pos hν _).ne') (by norm_num)
  rw [← hiff]
  simpa [g, IntegrableOn, integrable_const_mul_iff hc] using
    integrableOn_studentTBetaKernel_Ioi_iff hν hq

/-! ### Exponential moments -/

/-- The exponential of a nonzero multiple of the identity is not integrable under a Student t
law: if `exp (t * x)` and `exp (-t * x)` were both integrable, then every moment would be
finite, contradicting the sharp moment threshold `q < ν`. -/
theorem not_integrable_exp_mul_id_studentTMeasure (hν : 0 < ν) {t : ℝ} (ht : t ≠ 0) :
    ¬ Integrable (fun x : ℝ => Real.exp (t * x)) (studentTMeasure ν) := by
  intro hint
  -- reflection in the origin turns the rate `t` into `-t`
  have hmap : (studentTMeasure ν).map (fun x : ℝ => -x) = studentTMeasure ν :=
    studentTMeasure_map_neg ν
  have hkey : Integrable (fun y : ℝ => Real.exp (t * y))
      ((studentTMeasure ν).map (fun x : ℝ => -x)) := by
    rw [hmap]
    exact hint
  have hcomp : Integrable (fun x : ℝ => Real.exp (t * (-x))) (studentTMeasure ν) :=
    (integrable_map_measure hkey.aestronglyMeasurable measurable_neg.aemeasurable).mp hkey
  have hneg : Integrable (fun x : ℝ => Real.exp (-t * x)) (studentTMeasure ν) := by
    simpa [mul_neg] using hcomp
  -- both one-sided exponential moments would force every polynomial moment to be finite
  have hmom : Integrable (fun x : ℝ => |x| ^ ν) (studentTMeasure ν) :=
    integrable_rpow_abs_of_integrable_exp_mul ht hint hneg hν.le
  have hden : Integrable (fun x : ℝ => studentTPDFReal ν x * |x| ^ ν) :=
    (integrable_studentTMeasure_iff (ν := ν) (f := fun x : ℝ => |x| ^ ν)).mp hmom
  have hIoi : IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ ν) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun x : ℝ => studentTPDFReal ν x * |x| ^ ν) (Ioi (0 : ℝ)) :=
      hden.integrableOn
    have h2 : ∀ x ∈ Ioi (0 : ℝ), studentTPDFReal ν x * |x| ^ ν = studentTPDFReal ν x * x ^ ν := by
      intro x hx
      have hx0 : 0 < x := hx
      have habs : |x| = x := abs_of_pos hx0
      rw [habs]
    exact h1.congr_fun h2 measurableSet_Ioi
  have hq : -1 < ν := by linarith
  have : ν < ν := (integrableOn_pow_mul_studentTPDFReal_Ioi_iff hν hq).mp hIoi
  linarith

/-- The exponential integrand of a Student t law is integrable exactly at rate zero. -/
@[simp]
theorem integrable_exp_mul_id_studentTMeasure_iff (hν : 0 < ν) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (studentTMeasure ν) ↔ t = 0 := by
  have : IsProbabilityMeasure (studentTMeasure ν) :=
    isProbabilityMeasure_studentTMeasure hν
  refine ⟨fun h => not_ne_iff.mp fun ht => not_integrable_exp_mul_id_studentTMeasure hν ht h,
    fun ht => ?_⟩
  subst t
  have h : (fun x : ℝ => Real.exp (0 * x)) = fun _ : ℝ => (1 : ℝ) := by
    funext x
    simp
  rw [h]
  exact integrable_const (1 : ℝ)

/-- The exponential-integrability domain of the identity under a Student t law is the singleton
`{0}`: every nonzero exponential moment diverges in the polynomial tails. -/
@[simp]
theorem integrableExpSet_id_studentTMeasure (hν : 0 < ν) :
    integrableExpSet id (studentTMeasure ν) = {0} := by
  ext t
  simpa [integrableExpSet, id_eq] using integrable_exp_mul_id_studentTMeasure_iff hν t


end Probability

end TauCeti
