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

For a positive-semidefinite matrix `S`, the continuous-functional-calculus square root
`CFC.sqrt S` is again positive semidefinite, hence Hermitian. Sandwiching a Hermitian matrix `Θ`
between two copies of it gives the Hermitian matrix `CFC.sqrt S * Θ * CFC.sqrt S`. Its pencils
`1 - c • (CFC.sqrt S * Θ * CFC.sqrt S)` have the same determinant as those of `Θ * S`, by
Sylvester's determinant identity and `CFC.sqrt S * CFC.sqrt S = S`.

The sandwich is the matrix whose eigenvalues govern the exponential moments of a Gaussian
quadratic form, and the determinant identity is what turns its spectral formula into a formula
in the original parameters.

## Main results

* `Matrix.posSemidef_sqrt` and `Matrix.isHermitian_sqrt` — the square root is positive
  semidefinite and Hermitian, for every matrix;
* `Matrix.isHermitian_sqrt_mul_mul_sqrt` — the sandwich of a Hermitian matrix is Hermitian;
* `Matrix.det_one_sub_smul_sqrt_mul_mul_sqrt` — the pencil determinants agree.
-/

public section

noncomputable section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The square root of any matrix is positive semidefinite. For a matrix that is not positive
semidefinite the square root is `0`. -/
theorem posSemidef_sqrt (S : Matrix ι ι 𝕜) : (CFC.sqrt S).PosSemidef :=
  nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)

open scoped Classical in
/-- The square root of any matrix is Hermitian. -/
theorem isHermitian_sqrt (S : Matrix ι ι 𝕜) : (CFC.sqrt S).IsHermitian :=
  (posSemidef_sqrt S).1

open scoped Classical in
/-- Sandwiching a Hermitian matrix between two copies of a square root gives a Hermitian
matrix. -/
theorem isHermitian_sqrt_mul_mul_sqrt (S : Matrix ι ι 𝕜) {Θ : Matrix ι ι 𝕜}
    (hΘ : Θ.IsHermitian) : (CFC.sqrt S * Θ * CFC.sqrt S).IsHermitian := by
  simpa only [(isHermitian_sqrt S).eq] using isHermitian_conjTranspose_mul_mul (CFC.sqrt S) hΘ

/-- For positive-semidefinite `S`, the pencils of the sandwich `CFC.sqrt S * Θ * CFC.sqrt S` and
of the product `Θ * S` have the same determinant. -/
theorem det_one_sub_smul_sqrt_mul_mul_sqrt [DecidableEq ι] {S : Matrix ι ι 𝕜}
    (hS : S.PosSemidef) (Θ : Matrix ι ι 𝕜) (c : 𝕜) :
    (1 - c • (CFC.sqrt S * Θ * CFC.sqrt S)).det = (1 - c • (Θ * S)).det := by
  have hsq : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S (nonneg_iff_posSemidef.mpr hS)
  rw [← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul, ← Matrix.mul_assoc, hsq,
    ← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul]

end Matrix
