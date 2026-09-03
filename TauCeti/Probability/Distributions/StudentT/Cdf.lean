/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta
public import TauCeti.Probability.Distributions.StudentT.Basic
public import Mathlib.Probability.CDF
import TauCeti.Analysis.Calculus.RealCharts
import TauCeti.Probability.Distributions.StudentT.WeightedIntegral
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
    (injOn_sq_div_const_Ioi hν.ne').mono fun z hz => hy.trans_lt hz
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
  have hbeta_tail :
      ∫ w in Ioi (u0 / (1 - u0)), w ^ (-(1 / 2 : ℝ)) *
          (1 + w) ^ (-((ν + 1) / 2)) =
        beta (1 / 2) (ν / 2) *
          (1 - regularizedIncompleteBeta (1 / 2) (ν / 2) u0) := by
    have hb_pos : 0 < ν / 2 := by linarith
    have h := integral_Ioi_rpow_one_add_rpow_tail_eq (a := 1 / 2) (b := ν / 2)
      one_half_pos hb_pos hu00 hu01
    convert h using 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w _
    ring_nf
  rw [integral_Ioi_studentTPDFReal_eq_betaKernel_tail hν hy, ← hy0_eq,
    hbeta_tail]
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
