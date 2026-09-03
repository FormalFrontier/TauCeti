/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta
public import TauCeti.Probability.Distributions.StudentT.Basic
public import Mathlib.Probability.CDF
import TauCeti.Probability.Distributions.StudentT.WeightedIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The cumulative distribution function of Student's t law

This file computes the cumulative distribution function of the Student t distribution defined in
`TauCeti/Probability/Distributions/StudentT/Basic.lean`. On the positive half-line the substitution
`w = x ^ 2 / ν` turns the tail integral into Euler's second beta integral, and the substitution
`u = w / (1 + w)` then turns it into the regularized incomplete beta function.

## Main results

* `cdf_studentTMeasure_eq` — writing `z = ν / (ν + x ^ 2)`, the cdf is
  `regularizedIncompleteBeta (ν / 2) (1 / 2) z / 2` for `x < 0` and
  `1 - regularizedIncompleteBeta (ν / 2) (1 / 2) z / 2` for `0 ≤ x`.

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

/-! ### The cumulative distribution function -/

private lemma integral_Ioi_studentTPDFReal_eq_betaKernel_tail (hν : 0 < ν) {y : ℝ}
    (hy : 0 ≤ y) :
    ∫ z in Ioi y, studentTPDFReal ν z =
      (Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) *
          Real.rpow ν (1 / 2 : ℝ) / 2) *
        ∫ w in Ioi (y ^ 2 / ν), w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-((ν + 1) / 2)) := by
  set s := (ν + 1) / 2 with hs
  set C := Real.Gamma s / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) with hC
  set y0 := y ^ 2 / ν
  let g1 : ℝ → ℝ := fun w => C * ν ^ (1 / 2 : ℝ) / 2 *
      (w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-s))
  -- First change variables from the Student-t tail to the beta half-line kernel.
  have hinj : InjOn (fun z : ℝ => z ^ 2 / ν) (Ioi y) :=
    (sq_div_const_injOn_Ioi hν.ne').mono fun z hz => hy.trans_lt hz
  have hderiv1 : ∀ z ∈ Ioi y,
      HasDerivWithinAt (fun z : ℝ => z ^ 2 / ν) (2 * z / ν) (Ioi y) z :=
    fun z _ => (hasDerivAt_sq_div_const ν z).hasDerivWithinAt
  have h11 : ∫ w in Ioi y0, g1 w =
      ∫ z in Ioi y, |2 * z / ν| • g1 (z ^ 2 / ν) := by
    rw [← integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv1 hinj g1,
      image_sq_div_const_Ioi hν hy]
  have h12 : ∫ z in Ioi y, |2 * z / ν| • g1 (z ^ 2 / ν) =
      ∫ z in Ioi y, studentTPDFReal ν z := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    have hz0 : 0 < z := hy.trans_lt hz
    have h := abs_deriv_smul_studentTPDFReal hν 0 hz0
    have hhq : ((0 - 1) / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
    have h' : |2 * z / ν| • g1 (z ^ 2 / ν) = studentTPDFReal ν z := by
      have hrpow0 : Real.rpow ν (1 / 2 : ℝ) = Real.rpow ν ((0 + 1) / 2) := by
        congr 1; norm_num
      have hhs : s = (ν + 1) / 2 := hs.symm
      have hhqp : studentTBetaKernel ν 0 (z ^ 2 / ν) =
          (z ^ 2 / ν) ^ (-(1 / 2 : ℝ)) * (1 + z ^ 2 / ν) ^ (-s) := by
        simp only [studentTBetaKernel, hs, hhq]
      have hg1 : g1 (z ^ 2 / ν) =
          Real.Gamma s / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) *
            Real.rpow ν (1 / 2 : ℝ) / 2 *
            ((z ^ 2 / ν) ^ (-(1 / 2 : ℝ)) * (1 + z ^ 2 / ν) ^ (-s)) := by
        dsimp only [g1]
        rw [hC]; rfl
      have hg1' : g1 (z ^ 2 / ν) =
          Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) *
            Real.rpow ν ((0 + 1) / 2) / 2 * studentTBetaKernel ν 0 (z ^ 2 / ν) := by
        rw [hg1, hhqp, hhs, hrpow0]
      have h'' : |2 * z / ν| •
          (Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) *
            Real.rpow ν ((0 + 1) / 2) / 2 * studentTBetaKernel ν 0 (z ^ 2 / ν)) =
          studentTPDFReal ν z := by
        have h3 := h
        rw [Real.rpow_zero, mul_one] at h3
        exact h3
      rw [hg1']
      exact h''
    exact h'
  have h1 : ∫ z in Ioi y, studentTPDFReal ν z = ∫ w in Ioi y0, g1 w := by
    rw [← h12, ← h11]
  set K := C * Real.rpow ν (1 / 2 : ℝ) / 2 with hK
  have hg1 : ∫ w in Ioi y0, g1 w =
      K * ∫ w in Ioi y0, w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-s) := by
    have : g1 = fun w => K * (w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-s)) := by
      funext w
      simp only [g1, hK]
      rfl
    rw [this, integral_const_mul]
  rw [h1]
  rw [hg1]

/-- The half-line tail of Euler's second beta integral, written through the chart
`u ↦ u / (1 - u)`. -/
private lemma integral_Ioi_betaKernel_tail_eq_interval_tail {u0 : ℝ}
    (hu00 : 0 ≤ u0) (hu01 : u0 < 1) :
    ∫ w in Ioi (u0 / (1 - u0)), w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-((ν + 1) / 2)) =
      ∫ u in Ioo u0 1, u ^ (-(1 / 2 : ℝ)) * (1 - u) ^ (ν / 2 - 1) := by
  set s := (ν + 1) / 2 with hs
  have hderiv2 : ∀ u ∈ Ioo u0 1,
      HasDerivWithinAt (fun u : ℝ => u / (1 - u)) ((1 - u) ^ 2)⁻¹ (Ioo u0 1) u :=
    fun u hu => (hasDerivAt_div_one_sub (ne_of_lt hu.2)).hasDerivWithinAt
  let k0 : ℝ → ℝ := fun w => w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-s)
  let k : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ)) * (1 - u) ^ (ν / 2 - 1)
  -- The chart `u ↦ u / (1 - u)` turns the half-line beta tail into an interval tail.
  have hsub : Ioo u0 1 ⊆ Ioo (0 : ℝ) 1 := fun u hu =>
    ⟨by linarith [hu.1, hu00], hu.2⟩
  have hhabs : ∀ u ∈ Ioo u0 1, |((1 - u) ^ 2)⁻¹| = ((1 - u) ^ 2)⁻¹ := by
    intro u _
    have hnonneg : 0 ≤ ((1 - u) ^ 2)⁻¹ := by positivity
    exact abs_of_nonneg hnonneg
  have hcov : ∀ u ∈ Ioo u0 1, |((1 - u) ^ 2)⁻¹| • k0 (u / (1 - u)) = k u := by
    intro u hu
    have hk0 : k0 (u / (1 - u)) =
        (u / (1 - u)) ^ (-(1 / 2 : ℝ)) * (1 + u / (1 - u)) ^ (-s) := by
      simp [k0]
    rw [hk0]
    have hs' : s = (1 / 2 : ℝ) + ν / 2 := by dsimp only [s]; ring
    have ha : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by ring
    have hb : -((1 / 2 : ℝ) + ν / 2) = -s := by rw [← hs']
    have hkey := abs_deriv_smul_one_add_rpow (1 / 2 : ℝ) (ν / 2) (hsub hu)
    rw [ha, hb] at hkey
    exact hkey
  have hcov' : EqOn (fun u : ℝ => ((1 - u) ^ 2)⁻¹ • k0 (u / (1 - u))) k (Ioo u0 1) := by
    intro u hu
    have hc : ((1 - u) ^ 2)⁻¹ = |((1 - u) ^ 2)⁻¹| := (hhabs u hu).symm
    have hgoal : ((1 - u) ^ 2)⁻¹ • k0 (u / (1 - u)) = k u := by
      have hstep : ((1 - u) ^ 2)⁻¹ • k0 (u / (1 - u)) =
          |((1 - u) ^ 2)⁻¹| • k0 (u / (1 - u)) := by
        exact congr_arg (fun c : ℝ => c • k0 (u / (1 - u))) hc
      rw [hstep]
      exact hcov u hu
    exact hgoal
  have himg :
      (fun u : ℝ => u / (1 - u)) '' Ioo u0 1 = Ioi (u0 / (1 - u0)) := by
    rw [image_div_one_sub_Ioo hu01]
  have h21 : ∫ u in Ioo u0 1, |((1 - u) ^ 2)⁻¹| • k0 (u / (1 - u)) =
      ∫ w in Ioi (u0 / (1 - u0)), k0 w := by
    rw [← integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv2
        (div_one_sub_injOn_Ioo (u0 := u0)) k0, himg]
  have h22eq : EqOn (fun u : ℝ => |((1 - u) ^ 2)⁻¹| • k0 (u / (1 - u)))
      (fun u : ℝ => ((1 - u) ^ 2)⁻¹ • k0 (u / (1 - u))) (Ioo u0 1) := by
    intro u hu
    exact congr_arg (fun c : ℝ => c • k0 (u / (1 - u))) (hhabs u hu)
  have h22 : ∫ u in Ioo u0 1, |((1 - u) ^ 2)⁻¹| • k0 (u / (1 - u)) =
      ∫ u in Ioo u0 1, ((1 - u) ^ 2)⁻¹ • k0 (u / (1 - u)) := by
    rw [setIntegral_congr_fun measurableSet_Ioo h22eq]
  have h2 : ∫ w in Ioi (u0 / (1 - u0)), k0 w = ∫ u in Ioo u0 1, k u := by
    rw [← h21, h22, setIntegral_congr_fun measurableSet_Ioo hcov']
  simpa [k0, k, s] using h2

/-- The interval tail in the incomplete-beta chart is the total beta mass minus the normalized
lower incomplete beta mass. -/
private lemma integral_Ioo_rpow_one_sub_rpow_tail_eq (hν : 0 < ν) {u0 : ℝ} (hu00 : 0 ≤ u0)
    (hu01 : u0 < 1) :
    ∫ u in Ioo u0 1, u ^ (-(1 / 2 : ℝ)) * (1 - u) ^ (ν / 2 - 1) =
      beta (1 / 2) (ν / 2) *
        (1 - regularizedIncompleteBeta (1 / 2) (ν / 2) u0) := by
  let k : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ)) * (1 - u) ^ (ν / 2 - 1)
  let kb : ℝ → ℝ := fun t => t ^ ((1 / 2 : ℝ) - 1) * (1 - t) ^ (ν / 2 - 1)
  have hkeq : kb = k := by
    funext t
    have h : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by ring
    simp only [kb, k, h]
  have hb_pos : 0 < ν / 2 := by linarith
  have hmem01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmem11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hmemu0 : u0 ∈ Icc (0 : ℝ) 1 := ⟨hu00, by linarith⟩
  have hII : IntervalIntegrable kb volume 0 1 :=
    intervalIntegrable_rpow_mul_one_sub_rpow one_half_pos hb_pos hmem01 hmem11
  have hIIu : IntervalIntegrable kb volume 0 u0 :=
    intervalIntegrable_rpow_mul_one_sub_rpow one_half_pos hb_pos hmem01 hmemu0
  have hmemu0' : u0 ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact hmemu0
  have hmem11' : (1 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact hmem11
  have hII1 : IntervalIntegrable kb volume u0 1 :=
    hII.mono_set (Set.uIcc_subset_uIcc hmemu0' hmem11')
  have h41 : Ioo u0 1 =ᵐ[volume] Ioc u0 1 :=
    Ioo_ae_eq_Ioc' Real.volume_singleton
  have h4 : ∫ u in Ioo u0 1, k u = ∫ u in u0..(1 : ℝ), kb u := by
    rw [setIntegral_congr_set h41, ← hkeq,
      intervalIntegral.integral_of_le (by linarith : u0 ≤ 1)]
  have h5 := intervalIntegral.integral_add_adjacent_intervals hIIu hII1
  have h6 : ∫ t in (0 : ℝ)..(1 : ℝ), kb t = beta (1 / 2) (ν / 2) :=
    integral_rpow_mul_one_sub_rpow one_half_pos hb_pos
  -- Convert the interval tail into total beta mass minus the incomplete beta mass.
  have h3 : ∫ u in Ioo u0 1, k u = beta (1 / 2) (ν / 2) - ∫ u in (0 : ℝ)..u0, kb u := by
    rw [h4]
    linarith [h5, h6]
  have h71 : regularizedIncompleteBeta (1 / 2) (ν / 2) u0 =
      (∫ t in (0 : ℝ)..u0, kb t) / beta (1 / 2) (ν / 2) :=
    regularizedIncompleteBeta_def_of_mem_Icc one_half_pos hb_pos hmemu0
  have hbetane : beta (1 / 2) (ν / 2) ≠ 0 := (beta_pos one_half_pos hb_pos).ne'
  have h7 : ∫ t in (0 : ℝ)..u0, kb t =
      beta (1 / 2) (ν / 2) * regularizedIncompleteBeta (1 / 2) (ν / 2) u0 := by
    have : regularizedIncompleteBeta (1 / 2) (ν / 2) u0 =
        (∫ t in (0 : ℝ)..u0, kb t) / beta (1 / 2) (ν / 2) := h71
    have hgoal : (∫ t in (0 : ℝ)..u0, kb t) =
        beta (1 / 2) (ν / 2) * regularizedIncompleteBeta (1 / 2) (ν / 2) u0 := by
      rw [this]
      field_simp [hbetane]
    exact hgoal
  have htailval : beta (1 / 2) (ν / 2) -
      beta (1 / 2) (ν / 2) * regularizedIncompleteBeta (1 / 2) (ν / 2) u0 =
      beta (1 / 2) (ν / 2) *
        (1 - regularizedIncompleteBeta (1 / 2) (ν / 2) u0) := by ring
  have hgoal : ∫ u in Ioo u0 1, k u =
      beta (1 / 2) (ν / 2) * (1 - regularizedIncompleteBeta (1 / 2) (ν / 2) u0) := by
    rw [h3, h7, htailval]
  simpa [k] using hgoal

/-- The half-line tail of Euler's second beta integral, written through the chart
`u ↦ u / (1 - u)`. -/
private lemma integral_Ioi_betaKernel_tail_eq (hν : 0 < ν) {u0 : ℝ} (hu00 : 0 ≤ u0)
    (hu01 : u0 < 1) :
    ∫ w in Ioi (u0 / (1 - u0)), w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-((ν + 1) / 2)) =
      beta (1 / 2) (ν / 2) *
        (1 - regularizedIncompleteBeta (1 / 2) (ν / 2) u0) := by
  rw [integral_Ioi_betaKernel_tail_eq_interval_tail (ν := ν) hu00 hu01,
    integral_Ioo_rpow_one_sub_rpow_tail_eq hν hu00 hu01]

/-- The Student t normalizing constant times the beta-tail normalizer is `1 / 2`. -/
private lemma studentT_tail_normalizing_const (hν : 0 < ν) :
    Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) *
        Real.rpow ν (1 / 2 : ℝ) / 2 * beta (1 / 2) (ν / 2) = 1 / 2 := by
  set s := (ν + 1) / 2 with hs
  set C := Real.Gamma s / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) with hC
  have hsqrt : Real.sqrt (ν * Real.pi) = Real.sqrt ν * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul hν.le]
  have hrpow : Real.rpow ν (1 / 2 : ℝ) = Real.sqrt ν :=
    (Real.sqrt_eq_rpow ν).symm
  have hs' : s = 1 / 2 + ν / 2 := by dsimp only [s]; ring
  have hspos : 0 < s := by dsimp only [s]; linarith
  have hGnuv2 : Real.Gamma (ν / 2) ≠ 0 :=
    Real.Gamma_ne_zero fun m => by linarith
  have hbeta : beta (1 / 2) (ν / 2) =
      Real.Gamma (1 / 2) * Real.Gamma (ν / 2) / Real.Gamma s := by
    rw [ProbabilityTheory.beta, hs']
  calc
    Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) *
        Real.rpow ν (1 / 2 : ℝ) / 2 * beta (1 / 2) (ν / 2) =
      C * Real.rpow ν (1 / 2 : ℝ) / 2 *
        (Real.Gamma (1 / 2) * Real.Gamma (ν / 2) / Real.Gamma s) := by
          rw [hbeta, hC, hs]
    _ = 1 / 2 := by
      rw [hC, hrpow, hsqrt, Real.Gamma_one_half_eq]
      field_simp [hGnuv2, (Real.Gamma_pos_of_pos hspos).ne',
        Real.sqrt_ne_zero'.mpr hν, Real.sqrt_ne_zero'.mpr Real.pi_pos]

/-- The upper-tail integral of a valid Student t density: for `0 ≤ y`,
`P(y < T) = (1 - I_{y²/(ν+y²)}(1/2, ν/2)) / 2`. -/
private lemma integral_Ioi_studentTPDFReal_tail (hν : 0 < ν) {y : ℝ} (hy : 0 ≤ y) :
    ∫ z in Ioi y, studentTPDFReal ν z =
      (1 / 2 : ℝ) * (1 - regularizedIncompleteBeta (1 / 2) (ν / 2) (y ^ 2 / (ν + y ^ 2))) := by
  set u0 := y ^ 2 / (ν + y ^ 2)
  have hy0_eq : u0 / (1 - u0) = y ^ 2 / ν := by
    simp only [u0]
    field_simp [hν.ne']; ring
  have hu00 : 0 ≤ u0 := by positivity
  have hu01 : u0 < 1 := by
    simp only [u0]
    have h : y ^ 2 < ν + y ^ 2 := by linarith
    exact (div_lt_one (by positivity)).mpr h
  rw [integral_Ioi_studentTPDFReal_eq_betaKernel_tail hν hy, ← hy0_eq,
    integral_Ioi_betaKernel_tail_eq hν hu00 hu01]
  rw [← mul_assoc, studentT_tail_normalizing_const hν]

/-- **The cumulative distribution function of a Student t law.** Writing
`z = ν / (ν + x ^ 2)`, it is `regularizedIncompleteBeta (ν / 2) (1 / 2) z / 2` for `x < 0` and
`1 - regularizedIncompleteBeta (ν / 2) (1 / 2) z / 2` for `0 ≤ x`. -/
@[simp]
theorem cdf_studentTMeasure_eq (hν : 0 < ν) (x : ℝ) :
    cdf (studentTMeasure ν) x =
      if x < 0 then regularizedIncompleteBeta (ν / 2) (1 / 2) (ν / (ν + x ^ 2)) / 2
      else 1 - regularizedIncompleteBeta (ν / 2) (1 / 2) (ν / (ν + x ^ 2)) / 2 := by
  set z := ν / (ν + x ^ 2) with hz
  have : IsProbabilityMeasure (studentTMeasure ν) :=
    isProbabilityMeasure_studentTMeasure hν
  have hb_pos : 0 < ν / 2 := by linarith
  have htail : ∀ y : ℝ, 0 ≤ y →
      (studentTMeasure ν).real (Ioi y) =
        (1 / 2 : ℝ) * (1 - regularizedIncompleteBeta (1 / 2) (ν / 2) (y ^ 2 / (ν + y ^ 2))) := by
    intro y hy
    have hreal : (studentTMeasure ν).real (Ioi y) = ∫ z in Ioi y, studentTPDFReal ν z := by
      exact measureReal_studentTMeasure measurableSet_Ioi
    rw [hreal, integral_Ioi_studentTPDFReal_tail hν hy]
  by_cases hx : 0 ≤ x
  · -- nonnegative branch: `cdf = 1 - tail`, and the reflection formula swaps the beta parameters
    have hrefl : regularizedIncompleteBeta (1 / 2) (ν / 2) (x ^ 2 / (ν + x ^ 2)) =
        1 - regularizedIncompleteBeta (ν / 2) (1 / 2) z := by
      have h9 : 1 - x ^ 2 / (ν + x ^ 2) = z := by
        simp only [hz]; field_simp; ring
      rw [regularizedIncompleteBeta_symm one_half_pos hb_pos (x ^ 2 / (ν + x ^ 2)), h9]
    have huniv : (studentTMeasure ν).real univ = 1 := by
      rw [measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
    have htailx : (studentTMeasure ν).real (Ioi x) =
        regularizedIncompleteBeta (ν / 2) (1 / 2) z / 2 := by
      rw [htail x hx, hrefl]; ring
    have hcdf : (studentTMeasure ν).real (Iic x) =
        1 - regularizedIncompleteBeta (ν / 2) (1 / 2) z / 2 := by
      have hcomp : (studentTMeasure ν).real (Iic x) =
          (studentTMeasure ν).real univ - (studentTMeasure ν).real (Ioi x) := by
        rw [← measureReal_compl measurableSet_Ioi, compl_Ioi]
      rw [hcomp, huniv, htailx]
    rw [cdf_eq_real, hcdf, ite_eq_right (not_lt.mpr hx)]
  · -- negative branch: reflection in the origin gives `cdf(x) = tail(-x)`
    have hxneg : x < 0 := by linarith
    have hmy : 0 ≤ -x := by linarith
    have hpre : (fun w : ℝ => -w) ⁻¹' (Iic x) = Ici (-x) := by
      ext w
      simp [le_iff_eq_or_lt]
    have hnull : (studentTMeasure ν) ({-x} : Set ℝ) = 0 := by
      exact (studentTMeasure_absolutelyContinuous ν) (measure_singleton (-x))
    have h5 : Ici (-x) = Ioi (-x) ∪ ({-x} : Set ℝ) := by
      ext w
      simp [le_iff_eq_or_lt]
    have hdis : Disjoint (Ioi (-x)) ({-x} : Set ℝ) := by
      rw [Set.disjoint_left]
      intro w hw1 hw2
      have heq : w = -x := hw2
      rw [heq] at hw1
      exact lt_irrefl (-x) hw1
    have hcic : (studentTMeasure ν) (Ici (-x)) = (studentTMeasure ν) (Ioi (-x)) := by
      rw [h5, measure_union hdis (measurableSet_singleton _), hnull, add_zero]
    have hmap : (studentTMeasure ν).map (fun w : ℝ => -w) = studentTMeasure ν :=
      studentTMeasure_map_neg ν
    have hmap_apply : ∀ (t : Set ℝ), MeasurableSet t →
        ((studentTMeasure ν).map (fun w : ℝ => -w)) t =
          (studentTMeasure ν) ((fun w : ℝ => -w) ⁻¹' t) :=
      fun t ht => Measure.map_apply measurable_neg ht
    have h2 : (studentTMeasure ν) (Iic x) = (studentTMeasure ν) (Ici (-x)) := by
      have h3 : ((studentTMeasure ν).map (fun w : ℝ => -w)) (Iic x) =
          (studentTMeasure ν) (Ici (-x)) := by
        rw [hmap_apply (Iic x) measurableSet_Iic, hpre]
      have h4 : (studentTMeasure ν) (Iic x) =
          ((studentTMeasure ν).map (fun w : ℝ => -w)) (Iic x) := by
        rw [hmap]
      rw [h4, h3]
    have hreal : (studentTMeasure ν).real (Iic x) = (studentTMeasure ν).real (Ioi (-x)) := by
      rw [Measure.real, Measure.real, h2, hcic]
    have h9 : (-x) ^ 2 / (ν + (-x) ^ 2) = 1 - z := by
      simp only [hz, neg_sq]; field_simp; ring
    have hsym : regularizedIncompleteBeta (1 / 2) (ν / 2) (1 - z) =
        1 - regularizedIncompleteBeta (ν / 2) (1 / 2) z := by
      have h := regularizedIncompleteBeta_symm one_half_pos hb_pos (1 - z)
      have h12 : 1 - (1 - z) = z := by ring
      rw [h12] at h
      exact h
    have htailval : (studentTMeasure ν).real (Ioi (-x)) =
        (1 / 2 : ℝ) * regularizedIncompleteBeta (ν / 2) (1 / 2) z := by
      rw [htail (-x) hmy, h9, hsym]; ring
    have hcdf : (studentTMeasure ν).real (Iic x) =
        regularizedIncompleteBeta (ν / 2) (1 / 2) z / 2 := by
      rw [hreal, htailval]; ring
    rw [cdf_eq_real, hcdf, ite_eq_left hxneg]

end Probability

end TauCeti
