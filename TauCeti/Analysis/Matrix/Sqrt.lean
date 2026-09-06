/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Sandwiches by the square root of a positive-semidefinite matrix

Pulling the quadratic form `x ↦ ⟪x, B x⟫` of a matrix `B` back along the linear map of a matrix
`A` gives the quadratic form of the sandwich `Aᴴ * B * A`. This file records that identity and
specialises it to sandwiches by the continuous-functional-calculus square root `CFC.sqrt S` of a
matrix `S`, which is positive semidefinite (`CFC.sqrt_nonneg`), hence Hermitian. Sandwiching a
Hermitian matrix `Θ` between two copies of it gives the Hermitian matrix
`CFC.sqrt S * Θ * CFC.sqrt S`, whose pencils `1 - c • (CFC.sqrt S * Θ * CFC.sqrt S)` have the
same determinant as those of `Θ * S`, by Sylvester's determinant identity and
`CFC.sqrt S * CFC.sqrt S = S`.

The sandwich is the matrix whose eigenvalues govern the exponential moments of a Gaussian
quadratic form, and the determinant identity is what turns its spectral formula into a formula
in the original parameters.

## Main results

* `Matrix.inner_toEuclideanLin_toEuclideanLin` — the quadratic form of `B` at `A x` is the
  quadratic form of `Aᴴ * B * A` at `x`;
* `Matrix.isHermitian_sqrt_mul_mul_sqrt` — the sandwich of a Hermitian matrix by a square root
  is Hermitian;
* `Matrix.det_one_sub_smul_sqrt_mul_mul_sqrt` — the pencil determinants agree.
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- Pulling the quadratic form of `B` back along the linear map of `A` gives the quadratic form
of the sandwich `Aᴴ * B * A`. -/
theorem inner_toEuclideanLin_toEuclideanLin [DecidableEq ι] (A B : Matrix ι ι 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    ⟪A.toEuclideanLin x, B.toEuclideanLin (A.toEuclideanLin x)⟫_𝕜 =
      ⟪x, (Aᴴ * B * A).toEuclideanLin x⟫_𝕜 := by
  rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply]

open scoped Classical in
/-- Sandwiching a Hermitian matrix between two copies of a square root gives a Hermitian
matrix. -/
theorem isHermitian_sqrt_mul_mul_sqrt (S : Matrix ι ι 𝕜) {Θ : Matrix ι ι 𝕜}
    (hΘ : Θ.IsHermitian) : (CFC.sqrt S * Θ * CFC.sqrt S).IsHermitian := by
  simpa only [(Matrix.LE.le.posSemidef (CFC.sqrt_nonneg S)).1.eq] using
    isHermitian_conjTranspose_mul_mul (CFC.sqrt S) hΘ

/-- For positive-semidefinite `S`, the pencils of the sandwich `CFC.sqrt S * Θ * CFC.sqrt S` and
of the product `Θ * S` have the same determinant. -/
theorem det_one_sub_smul_sqrt_mul_mul_sqrt [DecidableEq ι] {S : Matrix ι ι 𝕜}
    (hS : S.PosSemidef) (Θ : Matrix ι ι 𝕜) (c : 𝕜) :
    (1 - c • (CFC.sqrt S * Θ * CFC.sqrt S)).det = (1 - c • (Θ * S)).det := by
  have hsq : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S hS.nonneg
  rw [← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul, ← Matrix.mul_assoc, hsq,
    ← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul]

end Matrix
