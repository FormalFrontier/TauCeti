/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Covariance matrices of Euclidean-valued measures

This file packages the coordinate covariances of a measure on a finite-dimensional Euclidean
space as a matrix and connects that matrix to Mathlib's basis-free `covarianceBilin`.

The `MemLp id 2 μ` hypothesis in the comparison theorem is essential. Mathlib deliberately sets
`covarianceBilin μ` to zero when this hypothesis fails, whereas its scalar `covariance` is
totalized coordinate by coordinate.

## Main results

* `TauCeti.covMatrix` is the matrix of coordinate covariances of a measure.
* `TauCeti.covarianceBilin_eq_covMatrix` identifies the matrix and bilinear-form views of
  covariance when the measure has a finite second moment.
* `TauCeti.posSemidef_covMatrix` proves that covariance matrices are positive semidefinite under
  the same moment hypotheses.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 1,
  **Covariance matrices**.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace

namespace TauCeti

variable {ι : Type*}


/-- The covariance matrix of a measure on a finite-dimensional Euclidean space. Its `(i, j)`
entry is the scalar covariance of the `i`th and `j`th coordinate projections. -/
def covMatrix (μ : Measure (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  fun i j => cov[fun z => z i, fun z => z j; μ]

/-- An entry of `covMatrix` is the covariance of the corresponding coordinate projections. -/
@[simp]
theorem covMatrix_apply (μ : Measure (EuclideanSpace ℝ ι)) (i j : ι) :
    covMatrix μ i j = cov[fun z => z i, fun z => z j; μ] := (rfl)

/-- Covariance matrices are symmetric. -/
theorem covMatrix_apply_comm (μ : Measure (EuclideanSpace ℝ ι)) (i j : ι) :
    covMatrix μ i j = covMatrix μ j i := by
  rw [covMatrix_apply, covMatrix_apply, covariance_comm]

/-- A covariance matrix is Hermitian (equivalently, symmetric over `ℝ`). -/
theorem isHermitian_covMatrix (μ : Measure (EuclideanSpace ℝ ι)) :
    (covMatrix μ).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
  exact fun i j => covMatrix_apply_comm μ j i

/-- For a finite measure with finite second moment, the entrywise covariance matrix represents
Mathlib's basis-free covariance bilinear form. -/
theorem covarianceBilin_eq_covMatrix [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ] (hμ : MemLp id 2 μ)
    (x y : EuclideanSpace ℝ ι) :
    covarianceBilin μ x y = ⟪x, (covMatrix μ).toEuclideanLin y⟫ := by
  classical
  have hcoord : ∀ i, MemLp (fun z : EuclideanSpace ℝ ι => z i) 2 μ := by
    intro i
    simpa only [id_eq, EuclideanSpace.coe_proj] using
      hμ.continuousLinearMap_comp (𝕜 := ℝ) (EuclideanSpace.proj i)
  have hpi := covarianceBilin_apply_pi (μ := μ) (X := fun i z => z i) hcoord x y
  have hfun : (fun z : EuclideanSpace ℝ ι => WithLp.toLp 2 (fun i => z i)) = id := by
    funext z
    exact WithLp.toLp_ofLp 2 z
  rw [hfun, Measure.map_id] at hpi
  rw [hpi]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [covMatrix_apply]
  ring

/-- The covariance matrix of a finite measure with finite second moment is positive semidefinite. -/
theorem posSemidef_covMatrix [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) :
    (covMatrix μ).PosSemidef := by
  classical
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr (isHermitian_covMatrix μ), fun x => ?_⟩
  have hnonneg := covarianceBilin_self_nonneg (μ := μ) x
  rw [covarianceBilin_eq_covMatrix μ hμ x x] at hnonneg
  simpa only [RCLike.re_to_real, real_inner_comm] using hnonneg

end TauCeti
