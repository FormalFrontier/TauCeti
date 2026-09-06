/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Moments.Covariance

/-!
# The covariance matrix of a multivariate Gaussian

This file identifies the generic covariance matrix from
`TauCeti.Probability.Moments.Covariance` with the covariance parameter of Mathlib's multivariate
Gaussian, and records the centred multivariate Gaussian as the image of the standard Gaussian
under the square root of its covariance matrix.

## Main results

* `TauCeti.covMatrix_multivariateGaussian` recovers the covariance parameter of a multivariate
  Gaussian law.
* `TauCeti.multivariateGaussian_zero_eq_map_sqrt` writes the centred law as an image of the
  standard Gaussian.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 1,
  **Covariance matrices**.
-/

public section

noncomputable section

open ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti

variable {ι : Type*}

/-- The covariance matrix of a positive-semidefinite multivariate Gaussian is its covariance
parameter. -/
@[simp]
theorem covMatrix_multivariateGaussian [Fintype ι] [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    covMatrix (multivariateGaussian m S) = S := by
  classical
  ext i j
  simpa only [covMatrix_apply] using covariance_eval_multivariateGaussian hS i j

/-- A centred multivariate Gaussian law is the image of the standard Gaussian under the square
root of its covariance matrix. -/
theorem multivariateGaussian_zero_eq_map_sqrt [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) :
    multivariateGaussian 0 S =
      (stdGaussian (EuclideanSpace ℝ ι)).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) := by
  simp [multivariateGaussian]

end TauCeti
