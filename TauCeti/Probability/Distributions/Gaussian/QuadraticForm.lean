/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.Matrix.Sqrt
public import TauCeti.Probability.Distributions.Gaussian.ChiSquared
public import TauCeti.Probability.Distributions.Gaussian.Multivariate

/-!
# Moment-generating functions of Gaussian quadratic forms

Let `S` be a covariance matrix and `Θ` a real symmetric matrix. This file determines exactly
when the quadratic statistic `x ↦ ⟪x, Θ x⟫` of a centred multivariate Gaussian vector has finite
exponential moments of order `t`, and computes its moment-generating function there:

* the integrand is integrable exactly when the pencil `1 - (2 * t) • (√S * Θ * √S)` is positive
  definite, where `√S = CFC.sqrt S`, with no hypothesis on `S`; and
* on that domain the moment-generating function is
  `det (1 - (2 * t) • (√S * Θ * √S)) ^ (-1 / 2)`, which for positive-semidefinite `S` is
  `det (1 - (2 * t) • (Θ * S)) ^ (-1 / 2)`.

The same results are stated for the standard Gaussian vector, in terms of the eigenvalues of the
symmetric matrix, and for one and for finitely many independent standard Gaussian coordinates,
where the quadratic form is a weighted sum of squares.

## Main results

* `TauCeti.mem_integrableExpSet_inner_toEuclideanLin_multivariateGaussian_iff` — the exact
  exponential-integrability domain of a Gaussian quadratic form;
* `TauCeti.mgf_inner_toEuclideanLin_multivariateGaussian_sqrt` and
  `TauCeti.mgf_inner_toEuclideanLin_multivariateGaussian` — its moment-generating function on
  that domain, in terms of the sandwich `√S * Θ * √S` and, for positive-semidefinite `S`, of
  `Θ * S`;
* `TauCeti.cgf_inner_toEuclideanLin_multivariateGaussian_sqrt` and
  `TauCeti.cgf_inner_toEuclideanLin_multivariateGaussian` — the cumulant-generating function, the
  real logarithm of the same values;
* `TauCeti.mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff` and
  `TauCeti.mgf_inner_toEuclideanLin_stdGaussian` — the same results for the standard Gaussian,
  in terms of the eigenvalues of the symmetric matrix;
* `TauCeti.mgf_sum_mul_sq_pi_gaussianReal_eq_prod` — the moment-generating function of a
  weighted sum of squares of independent standard Gaussian coordinates factors over the
  coordinates, for every `t`.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 1.2.6
  (the multivariate Gaussian) and Theorem 3.2.3 (the Wishart moment-generating function, which
  is the product of these).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti

/-! ### One standard Gaussian coordinate -/

section scalar

variable {w t : ℝ}

/-- The exponential moment of order `t` of `w * x ^ 2` under the standard Gaussian is finite
exactly when `2 * t * w < 1`. -/
theorem mem_integrableExpSet_mul_sq_gaussianReal_iff (w t : ℝ) :
    t ∈ integrableExpSet (fun x ↦ w * x ^ 2) (gaussianReal 0 1) ↔ 2 * t * w < 1 := by
  have key : t ∈ integrableExpSet (fun x ↦ w * x ^ 2) (gaussianReal 0 1) ↔
      t * w ∈ integrableExpSet id (Probability.chiSquaredMeasure 1) := by
    simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq]
    rw [← Probability.gaussianReal_map_sq,
      integrable_map_measure (by fun_prop) (by fun_prop), Function.comp_def]
    simp only [mul_assoc]
  rw [key, Probability.integrableExpSet_id_chiSquaredMeasure zero_lt_one, Set.mem_Iio]
  constructor <;> intro h <;> linarith

/-- The moment-generating function of `w * x ^ 2` under the standard Gaussian is
`(1 - 2 * t * w) ^ (-1 / 2)` on its domain `2 * t * w < 1`. -/
theorem mgf_mul_sq_gaussianReal (ht : 2 * t * w < 1) :
    mgf (fun x ↦ w * x ^ 2) (gaussianReal 0 1) t = (1 - 2 * t * w) ^ (-1 / 2 : ℝ) := by
  rw [mgf_const_mul, ← mgf_id_map (X := fun x : ℝ ↦ x ^ 2) (by fun_prop),
    Probability.gaussianReal_map_sq,
    Probability.mgf_id_chiSquaredMeasure zero_le_one (by linarith),
    mul_comm w t, ← mul_assoc]
  norm_num

end scalar

/-! ### Independent standard Gaussian coordinates -/

section pi

variable {ι : Type*} [Fintype ι] {w : ι → ℝ} {t : ℝ}

/-- Under a product measure the exponential of a weighted sum of squares factors over the
coordinates, so Fubini's theorem turns its integral into a product of one-dimensional
moment-generating functions. No integrability hypothesis is needed: off the common domain both
sides are zero. -/
theorem mgf_sum_mul_sq_pi_gaussianReal_eq_prod (w : ι → ℝ) (t : ℝ) :
    mgf (fun c : ι → ℝ ↦ ∑ j, w j * c j ^ 2)
        (Measure.pi fun _ : ι ↦ gaussianReal 0 1) t =
      ∏ j, mgf (fun u : ℝ ↦ w j * u ^ 2) (gaussianReal 0 1) t := by
  simp only [mgf, Finset.mul_sum, Real.exp_sum]
  exact integral_fintype_prod_eq_prod fun j (u : ℝ) ↦ Real.exp (t * (w j * u ^ 2))

/-- The exponential moment of order `t` of the weighted sum of squares `∑ j, w j * c j ^ 2` of
independent standard Gaussian coordinates is finite exactly when `2 * t * w j < 1` for every
`j`. -/
theorem mem_integrableExpSet_sum_mul_sq_pi_gaussianReal_iff (w : ι → ℝ) (t : ℝ) :
    t ∈ integrableExpSet (fun c : ι → ℝ ↦ ∑ j, w j * c j ^ 2)
        (Measure.pi fun _ : ι ↦ gaussianReal 0 1) ↔
      ∀ j, 2 * t * w j < 1 := by
  have hpos (j : ι) :
      0 < mgf (fun u : ℝ ↦ w j * u ^ 2) (gaussianReal 0 1) t ↔ 2 * t * w j < 1 := by
    rw [mgf_pos_iff]
    exact mem_integrableExpSet_mul_sq_gaussianReal_iff (w j) t
  have hmem : t ∈ integrableExpSet (fun c : ι → ℝ ↦ ∑ j, w j * c j ^ 2)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) ↔
      0 < ∏ j, mgf (fun u : ℝ ↦ w j * u ^ 2) (gaussianReal 0 1) t := by
    rw [← mgf_sum_mul_sq_pi_gaussianReal_eq_prod]
    exact mgf_pos_iff.symm
  rw [hmem]
  refine ⟨fun h j ↦ (hpos j).1 (mgf_nonneg.lt_of_ne' fun hj ↦ ?_),
    fun h ↦ Finset.prod_pos fun j _ ↦ (hpos j).2 (h j)⟩
  exact absurd (Finset.prod_eq_zero (Finset.mem_univ j) hj) h.ne'

/-- The moment-generating function of the weighted sum of squares `∑ j, w j * c j ^ 2` of
independent standard Gaussian coordinates is `∏ j, (1 - 2 * t * w j) ^ (-1 / 2)` on its
domain. -/
theorem mgf_sum_mul_sq_pi_gaussianReal (ht : ∀ j, 2 * t * w j < 1) :
    mgf (fun c : ι → ℝ ↦ ∑ j, w j * c j ^ 2)
        (Measure.pi fun _ : ι ↦ gaussianReal 0 1) t =
      ∏ j, (1 - 2 * t * w j) ^ (-1 / 2 : ℝ) := by
  rw [mgf_sum_mul_sq_pi_gaussianReal_eq_prod]
  exact Finset.prod_congr rfl fun j _ ↦ mgf_mul_sq_gaussianReal (ht j)

end pi

/-! ### The standard Gaussian vector -/

section stdGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℝ} (hB : B.IsHermitian)
  {t : ℝ}
include hB

/-- The exponential moment of order `t` of the quadratic form of a real symmetric matrix `B`
under the standard Gaussian vector is finite exactly when `2 * t * λ < 1` for every eigenvalue
`λ` of `B`. -/
theorem mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff (t : ℝ) :
    t ∈ integrableExpSet (fun x ↦ ⟪x, B.toEuclideanLin x⟫)
        (stdGaussian (EuclideanSpace ℝ ι)) ↔
      ∀ j, 2 * t * hB.eigenvalues j < 1 := by
  rw [← mem_integrableExpSet_sum_mul_sq_pi_gaussianReal_iff hB.eigenvalues t]
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  rw [stdGaussian_eq_map_pi_orthonormalBasis hB.eigenvectorBasis,
    integrable_map_measure (by fun_prop) (Measurable.aemeasurable (by fun_prop)),
    Function.comp_def]
  simp only [hB.inner_toEuclideanLin_sum_smul_eigenvectorBasis]

/-- The moment-generating function of the quadratic form of a real symmetric matrix `B` under
the standard Gaussian vector is `∏ j, (1 - 2 * t * λ j) ^ (-1 / 2)` over the eigenvalues `λ j`
of `B`, on its domain. -/
theorem mgf_inner_toEuclideanLin_stdGaussian (ht : ∀ j, 2 * t * hB.eigenvalues j < 1) :
    mgf (fun x ↦ ⟪x, B.toEuclideanLin x⟫) (stdGaussian (EuclideanSpace ℝ ι)) t =
      ∏ j, (1 - 2 * t * hB.eigenvalues j) ^ (-1 / 2 : ℝ) := by
  rw [← mgf_sum_mul_sq_pi_gaussianReal ht,
    stdGaussian_eq_map_pi_orthonormalBasis hB.eigenvectorBasis,
    mgf_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop), Function.comp_def]
  simp only [hB.inner_toEuclideanLin_sum_smul_eigenvectorBasis]

end stdGaussian

/-! ### The centred multivariate Gaussian vector -/

section multivariateGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S Θ : Matrix ι ι ℝ} {t : ℝ}

/-- The exponential moment of order `t` of the quadratic form `x ↦ ⟪x, Θ x⟫` of a real
symmetric matrix `Θ` under the centred multivariate Gaussian with covariance `S` is finite
exactly when the pencil `1 - (2 * t) • (√S * Θ * √S)` is positive definite.

No hypothesis on `S` is needed: for a covariance matrix that is not positive semidefinite,
Mathlib's `CFC.sqrt S` is zero, the pencil is the identity, and the law is the Dirac measure
at the origin. -/
theorem mem_integrableExpSet_inner_toEuclideanLin_multivariateGaussian_iff (S : Matrix ι ι ℝ)
    (hΘ : Θ.IsHermitian) (t : ℝ) :
    t ∈ integrableExpSet (fun x ↦ ⟪x, Θ.toEuclideanLin x⟫)
        (multivariateGaussian 0 S) ↔
      (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).PosDef := by
  have hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S hΘ
  rw [hB.posDef_one_sub_smul_iff,
    ← mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff hB t,
    multivariateGaussian_zero_eq_map_sqrt]
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  rw [integrable_map_measure (by fun_prop) (Measurable.aemeasurable (by fun_prop)),
    Function.comp_def]
  simp only [← ContinuousLinearMap.coe_coe, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    Matrix.inner_toEuclideanLin_toEuclideanLin, (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg S)).1.eq]

/-- On its exponential-integrability domain, the moment-generating function of the quadratic
form `x ↦ ⟪x, Θ x⟫` of a real symmetric matrix `Θ` under the centred multivariate Gaussian
with covariance `S` is `det (1 - (2 * t) • (√S * Θ * √S)) ^ (-1 / 2)`, for every `S`. -/
theorem mgf_inner_toEuclideanLin_multivariateGaussian_sqrt (S : Matrix ι ι ℝ)
    (hΘ : Θ.IsHermitian) (ht : (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).PosDef) :
    mgf (fun x ↦ ⟪x, Θ.toEuclideanLin x⟫) (multivariateGaussian 0 S) t =
      (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).det ^ (-1 / 2 : ℝ) := by
  have hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S hΘ
  have ht' : ∀ j, 2 * t * hB.eigenvalues j < 1 := (hB.posDef_one_sub_smul_iff (2 * t)).1 ht
  rw [multivariateGaussian_zero_eq_map_sqrt,
    mgf_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop), Function.comp_def]
  simp only [← ContinuousLinearMap.coe_coe, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    Matrix.inner_toEuclideanLin_toEuclideanLin, (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg S)).1.eq]
  rw [mgf_inner_toEuclideanLin_stdGaussian hB ht',
    Real.finsetProd_rpow _ _ (fun j _ ↦ by linarith [ht' j]) _, ← hB.det_one_sub_smul (2 * t)]

/-- On its exponential-integrability domain, the cumulant-generating function of the quadratic
form `x ↦ ⟪x, Θ x⟫` of a real symmetric matrix `Θ` under the centred multivariate Gaussian
with covariance `S` is the real logarithm of `det (1 - (2 * t) • (√S * Θ * √S)) ^ (-1 / 2)`,
for every `S`. -/
theorem cgf_inner_toEuclideanLin_multivariateGaussian_sqrt (S : Matrix ι ι ℝ)
    (hΘ : Θ.IsHermitian) (ht : (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).PosDef) :
    cgf (fun x ↦ ⟪x, Θ.toEuclideanLin x⟫) (multivariateGaussian 0 S) t =
      Real.log ((1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).det ^ (-1 / 2 : ℝ)) := by
  rw [cgf, mgf_inner_toEuclideanLin_multivariateGaussian_sqrt S hΘ ht]

/-- On its exponential-integrability domain, the moment-generating function of the quadratic
form `x ↦ ⟪x, Θ x⟫` of a real symmetric matrix `Θ` under the centred multivariate Gaussian
with positive-semidefinite covariance `S` is `det (1 - (2 * t) • (Θ * S)) ^ (-1 / 2)`. -/
theorem mgf_inner_toEuclideanLin_multivariateGaussian (hS : S.PosSemidef) (hΘ : Θ.IsHermitian)
    (ht : (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).PosDef) :
    mgf (fun x ↦ ⟪x, Θ.toEuclideanLin x⟫) (multivariateGaussian 0 S) t =
      (1 - (2 * t) • (Θ * S)).det ^ (-1 / 2 : ℝ) := by
  rw [mgf_inner_toEuclideanLin_multivariateGaussian_sqrt S hΘ ht,
    hS.det_one_sub_smul_sqrt_mul_mul_sqrt Θ (2 * t)]

/-- On its exponential-integrability domain, the cumulant-generating function of the quadratic
form `x ↦ ⟪x, Θ x⟫` of a real symmetric matrix `Θ` under the centred multivariate Gaussian
with positive-semidefinite covariance `S` is the real logarithm of
`det (1 - (2 * t) • (Θ * S)) ^ (-1 / 2)`. -/
theorem cgf_inner_toEuclideanLin_multivariateGaussian (hS : S.PosSemidef)
    (hΘ : Θ.IsHermitian) (ht : (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).PosDef) :
    cgf (fun x ↦ ⟪x, Θ.toEuclideanLin x⟫) (multivariateGaussian 0 S) t =
      Real.log ((1 - (2 * t) • (Θ * S)).det ^ (-1 / 2 : ℝ)) := by
  rw [cgf, mgf_inner_toEuclideanLin_multivariateGaussian hS hΘ ht]

end multivariateGaussian

end TauCeti
