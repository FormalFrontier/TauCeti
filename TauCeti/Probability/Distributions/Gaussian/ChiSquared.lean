/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.ChiSquared
public import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# Squares of standard Gaussian variables

This file identifies the square of a standard real Gaussian variable with the chi-squared law
of one degree of freedom. It then combines this identification with independence to prove that
the sum of the squares of a finite independent standard Gaussian family has the chi-squared law
whose degrees of freedom are the cardinality of the family. The empty family is included: both
the empty sum and `chiSquaredMeasure 0` are the point mass at zero.

These laws identify Gaussian quadratic statistics with chi-squared distributions. In particular,
they provide the scalar foundation for distributional results about Gaussian norms and Gaussian
Gram matrices.

## Main results

* `TauCeti.Probability.gaussianReal_map_sq` — the square of the standard Gaussian measure is
  `chiSquaredMeasure 1`;
* `TauCeti.Probability.iIndepFun.hasLaw_sum_sq_gaussian` — a finite sum of independent squared
  standard Gaussian variables has the corresponding chi-squared law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), ch. 18.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The image of the standard Gaussian law under squaring is the chi-squared law with one degree
of freedom. -/
@[simp]
theorem gaussianReal_map_sq :
    (gaussianReal 0 1).map (fun x : ℝ ↦ x ^ 2) = chiSquaredMeasure 1 := by
  let _ : IsProbabilityMeasure (chiSquaredMeasure 1) :=
    isProbabilityMeasure_chiSquaredMeasure zero_le_one
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    cdf_chiSquaredMeasure_eq zero_lt_one]
  by_cases hx : x < 0
  · have hpreimage : (fun y : ℝ ↦ y ^ 2) ⁻¹' Iic x = ∅ := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact fun hy ↦ (not_le_of_gt hx) ((sq_nonneg y).trans hy)
    rw [hpreimage, measureReal_empty,
      regularizedGamma_eq_zero_of_nonpos_right (1 / 2) (by linarith)]
  · have hx' : 0 ≤ x := le_of_not_gt hx
    have hpreimage : (fun y : ℝ ↦ y ^ 2) ⁻¹' Iic x = Icc (-√x) √x := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_Icc]
      constructor
      · exact fun hy ↦ abs_le.mp (Real.abs_le_sqrt hy)
      · intro hy
        rw [← Real.sq_sqrt hx']
        exact sq_le_sq' hy.1 hy.2
    rw [hpreimage]
    let _ : NullSingletonClass (gaussianReal 0 1) :=
      nullSingletonClass_gaussianReal one_ne_zero
    have hIoc :
        (gaussianReal 0 1).real (Ioc (-√x) √x) =
          cdf (gaussianReal 0 1) √x - cdf (gaussianReal 0 1) (-√x) := by
      calc
        (gaussianReal 0 1).real (Ioc (-√x) √x) =
            (cdf (gaussianReal 0 1)).measure.real (Ioc (-√x) √x) := by
          rw [measure_cdf]
        _ = cdf (gaussianReal 0 1) √x - cdf (gaussianReal 0 1) (-√x) := by
          rw [Measure.real, StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal]
          exact sub_nonneg.mpr ((cdf (gaussianReal 0 1)).mono (by linarith [Real.sqrt_nonneg x]))
    rw [← measureReal_congr (Ioc_ae_eq_Icc (a := -√x) (b := √x)),
      hIoc, cdf_gaussianReal_zero_one, cdf_gaussianReal_zero_one]
    have hneg : -√x / √2 = -(√x / √2) := by ring
    rw [hneg, Real.erf_neg]
    have herf : 0 ≤ √x / √2 := by positivity
    rw [Real.erf_eq_regularizedGamma_half_sq herf]
    rw [div_pow, Real.sq_sqrt hx', Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
    ring

variable {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota] {P : Measure Omega}
  {X : iota → Omega → ℝ}

/-- A finite sum of squares of independent standard Gaussian variables has the chi-squared law
with one degree of freedom per variable. This includes an empty index type, when both sides are
the point mass at zero. -/
theorem iIndepFun.hasLaw_sum_sq_gaussian (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 1) P) :
    HasLaw (fun omega ↦ ∑ i, X i omega ^ 2) (chiSquaredMeasure (Fintype.card iota)) P := by
  have hsquareLaw :
      HasLaw (fun x : ℝ ↦ x ^ 2) (chiSquaredMeasure 1) (gaussianReal 0 1) :=
    ⟨by fun_prop, gaussianReal_map_sq⟩
  have hlawSq (i : iota) :
      HasLaw (fun omega ↦ X i omega ^ 2) (chiSquaredMeasure 1) P := by
    simpa [Function.comp_def] using hsquareLaw.comp (hlaw i)
  have hindepSq : iIndepFun (fun i omega ↦ X i omega ^ 2) P := by
    simpa [Function.comp_def] using
      hindep.comp (fun (_ : iota) (x : ℝ) ↦ x ^ 2) (fun _ ↦ by fun_prop)
  simpa using iIndepFun.hasLaw_sum_chiSquared hindepSq (fun _ ↦ zero_le_one) hlawSq

end Probability

end TauCeti
