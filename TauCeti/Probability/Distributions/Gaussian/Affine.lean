/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Multivariate

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Affine images of multivariate Gaussian measures

This file proves that a multivariate Gaussian measure is carried by a rectangular affine map to
the multivariate Gaussian with the transformed mean and covariance.  Rectangular matrices are
allowed, so the result applies both to embeddings and to possibly singular projections.

## Main result

* `TauCeti.map_affine_multivariateGaussian`: the affine pushforward formula for a multivariate
  Gaussian measure.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*.
* `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 3, **Affine maps of Gaussian
  laws**.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The covariance form of an affine image of a multivariate Gaussian is the one belonging to the
congruated matrix `L * S * Lᵀ`. The map `L` may be rectangular; no rank hypothesis is needed. -/
private theorem covarianceBilin_map_affine_multivariateGaussian (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (L : Matrix κ ι ℝ) (c : EuclideanSpace ℝ κ) :
    covarianceBilin
        (((multivariateGaussian m S).map L.toEuclideanLin.toContinuousLinearMap).map
          fun y => y + c) =
      covarianceBilin
        (multivariateGaussian (L.toEuclideanLin m + c) (L * S * L.transpose)) := by
  set T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
    L.toEuclideanLin.toContinuousLinearMap with hT
  -- The covariance API states translation with the constant on the left.
  have h_translate : (fun y : EuclideanSpace ℝ κ => y + c) = fun y => c + y := by
    funext y
    exact add_comm y c
  rw [h_translate]
  rw [covarianceBilin_map_const_add]
  ext x y
  -- Over `ℝ` the conjugate transpose is the ordinary transpose, so the congruate is positive
  -- semidefinite with no rank hypothesis on the rectangular matrix.
  have hLS : (L * S * L.transpose).PosSemidef := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial L]
    exact hS.mul_mul_conjTranspose_same L
  have hTadj : T.adjoint = L.transpose.toEuclideanLin.toContinuousLinearMap := by
    rw [← LinearMap.adjoint_toContinuousLinearMap]
    congr 1
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial L]
  rw [covarianceBilin_map IsGaussian.memLp_two_id,
    covarianceBilin_multivariateGaussian hS,
    covarianceBilin_multivariateGaussian hLS, hTadj]
  simp only [LinearMap.coe_toContinuousLinearMap']
  have h_apply (z : EuclideanSpace ℝ κ) :
      (L.transpose.toEuclideanLin z).ofLp = Matrix.mulVec L.transpose z.ofLp := by
    simpa only [Matrix.toLin'_apply] using
      Matrix.ofLp_toLpLin (p := 2) (q := 2) L.transpose z
  rw [h_apply, h_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  calc
    L.transpose.mulVec x.ofLp ⬝ᵥ S.mulVec (L.transpose.mulVec y.ofLp) =
        Matrix.vecMul x.ofLp L ⬝ᵥ S.mulVec (L.transpose.mulVec y.ofLp) := by
      rw [Matrix.mulVec_transpose]
    _ = x.ofLp ⬝ᵥ L.mulVec (S.mulVec (L.transpose.mulVec y.ofLp)) :=
      (Matrix.dotProduct_mulVec x.ofLp L
        (S.mulVec (L.transpose.mulVec y.ofLp))).symm

/-- The image of a multivariate Gaussian under a rectangular affine map is the multivariate
Gaussian with the corresponding transformed mean and covariance. -/
@[simp]
theorem map_affine_multivariateGaussian (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (L : Matrix κ ι ℝ) (c : EuclideanSpace ℝ κ) :
    (multivariateGaussian m S).map (fun x => L.toEuclideanLin x + c) =
      multivariateGaussian (L.toEuclideanLin m + c) (L * S * L.transpose) := by
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
    L.toEuclideanLin.toContinuousLinearMap
  -- Separate the linear image from the translation so that Mathlib's covariance rules apply.
  have h_map :
      (multivariateGaussian m S).map (fun x => L.toEuclideanLin x + c) =
        ((multivariateGaussian m S).map T).map (fun y => y + c) := by
    rw [Measure.map_map]
    · refine congrArg (fun f => (multivariateGaussian m S).map f) ?_
      funext x
      simp only [T, Function.comp_apply, LinearMap.coe_toContinuousLinearMap']
    · fun_prop
    · fun_prop
  rw [h_map]
  -- Gaussian measures are determined by their mean and covariance bilinear form.
  apply IsGaussian.ext
  · rw [integral_map]
    · simp only [id_eq]
      rw [integral_id_multivariateGaussian]
      calc
        ∫ x, x + c ∂(multivariateGaussian m S).map T =
            (∫ x, x ∂(multivariateGaussian m S).map T) +
              ∫ _x, c ∂(multivariateGaussian m S).map T :=
          integral_add IsGaussian.integrable_id (integrable_const c)
        _ = T m + c := by
          rw [T.integral_id_map IsGaussian.integrable_id, integral_id_multivariateGaussian,
            integral_const]
          simp
        _ = L.toEuclideanLin m + c := by
          simp only [T, LinearMap.coe_toContinuousLinearMap']
    · fun_prop
    · fun_prop
  · exact covarianceBilin_map_affine_multivariateGaussian m hS L c

end TauCeti
