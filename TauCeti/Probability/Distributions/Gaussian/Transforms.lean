/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Basic

import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Moment-generating functions of Gaussian linear functionals

This file proves that every continuous linear functional of a Gaussian measure has finite
exponential moments of every real order and computes its moment-generating function. It then
specializes the general result to inner products against a multivariate Gaussian vector, expressing
the variance as the covariance-matrix quadratic form.

## Main results

* `ProbabilityTheory.IsGaussian.integrableExpSet_dual` identifies the exponential-integrability
  domain of a continuous linear functional of a Gaussian measure with all of `ℝ`.
* `ProbabilityTheory.IsGaussian.mgf_dual` computes its moment-generating function from its mean and
  variance.
* `TauCeti.integrableExpSet_inner_multivariateGaussian` gives the exact domain for a directional
  functional of a multivariate Gaussian.
* `TauCeti.mgf_inner_toEuclideanLin_multivariateGaussian` gives the corresponding closed formula.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, IMS Lecture Notes--Monograph
  Series 53.
* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 3,
  **Affine maps of Gaussian laws**.
-/

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory

namespace IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {μ : Measure E} [IsGaussian μ]

/-- A continuous linear functional of a Gaussian measure has finite exponential moments of every
real order. -/
theorem integrableExpSet_dual (L : StrongDual ℝ E) : integrableExpSet L μ = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro t
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  refine (integrable_map_measure (f := L) (g := fun x : ℝ ↦ Real.exp (t * x))
    (by fun_prop) L.continuous.measurable.aemeasurable).mp ?_
  rw [IsGaussian.map_eq_gaussianReal L]
  exact integrable_exp_mul_gaussianReal t

/-- The moment-generating function of a continuous linear functional of a Gaussian measure is
determined by its mean and variance. -/
theorem mgf_dual (L : StrongDual ℝ E) (t : ℝ) :
    mgf L μ t = Real.exp (t * μ[L] + t ^ 2 / 2 * Var[L; μ]) := by
  rw [← mgf_id_map L.continuous.measurable.aemeasurable,
    IsGaussian.map_eq_gaussianReal L, mgf_id_gaussianReal]
  rw [Real.coe_toNNReal _ (variance_nonneg _ _)]
  ring_nf

end IsGaussian

end ProbabilityTheory

open ProbabilityTheory
open scoped RealInnerProductSpace

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every directional linear functional of a multivariate Gaussian has finite exponential moments
of all real orders.

This remains true for a covariance matrix that is not positive semidefinite: Mathlib then
totalizes the multivariate Gaussian to a Dirac measure at its mean. -/
theorem integrableExpSet_inner_multivariateGaussian (m θ : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) :
    integrableExpSet (fun x ↦ ⟪θ, x⟫) (multivariateGaussian m S) = Set.univ := by
  simpa only [coe_innerSL_apply] using
    IsGaussian.integrableExpSet_dual (μ := multivariateGaussian m S) (innerSL ℝ θ)

/-- The moment-generating function of the inner product against a multivariate Gaussian vector.

The exponent consists of the directional mean and one half of the covariance quadratic form,
scaled respectively by `t` and `t²`. -/
theorem mgf_inner_toEuclideanLin_multivariateGaussian (m θ : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (t : ℝ) :
    mgf (fun x ↦ ⟪θ, x⟫) (multivariateGaussian m S) t =
      Real.exp (t * ⟪θ, m⟫ + t ^ 2 / 2 * ⟪θ, S.toEuclideanLin θ⟫) := by
  let L : StrongDual ℝ (EuclideanSpace ℝ ι) := innerSL ℝ θ
  have hL : (fun x ↦ ⟪θ, x⟫) = L := by
    ext
    simp [L, innerSL_apply_apply]
  have hmean : ∫ x, L x ∂multivariateGaussian m S = ⟪θ, m⟫ := by
    calc
      ∫ x, L x ∂multivariateGaussian m S =
          L (∫ x, x ∂multivariateGaussian m S) := by
            simpa only [Function.comp_apply, id_eq] using
              L.integral_comp_comm (IsGaussian.integrable_id (μ := multivariateGaussian m S))
      _ = ⟪θ, m⟫ := by simp [L, innerSL_apply_apply]
  have hvar : Var[L; multivariateGaussian m S] = ⟪θ, S.toEuclideanLin θ⟫ := by
    rw [← hL]
    rw [← covariance_self (by fun_prop),
      ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hS]
    exact (Matrix.inner_toEuclideanCLM S θ θ).symm
  rw [hL, IsGaussian.mgf_dual, hmean, hvar]

end TauCeti
