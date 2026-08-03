/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Geometry.Lie.Exponential.UnitsCompatibility

/-!
# Compatibility with the matrix exponential

The abstract Lie-group exponential on the general linear group is the usual matrix exponential.
The remaining results show that the transported abstract exponential inherits Mathlib's diagonal,
transpose, and conjugation formulas.

## Main results

* `lieExp_generalLinearGroup_coe`: the abstract exponential, transported from the Lie algebra of
  `GL(n, ℝ)` to matrices, is `NormedSpace.exp`.
* `lieExp_generalLinearGroup_diagonal`: the abstract exponential of a diagonal matrix is diagonal.
* `lieExp_generalLinearGroup_transpose`: the abstract exponential commutes with transpose.
* `lieExp_generalLinearGroup_conj`: the abstract exponential respects conjugation.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The matrix and circle shadows".
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coercing the abstract exponential on `GL(n, ℝ)` to matrices gives the matrix exponential. -/
@[simp]
theorem lieExp_generalLinearGroup_coe (A : Matrix n n ℝ) :
    ((lieExp
        ((unitsLieAlgebraEquiv (R := Matrix n n ℝ)).symm A) :
          Matrix.GeneralLinearGroup n ℝ) : Matrix n n ℝ) = exp A := by
  rw [lieExp_eq_expUnit, LinearEquiv.apply_symm_apply, TauCeti.expUnit_coe]
  rfl

/-- The abstract exponential on `GL(n, ℝ)` sends diagonal matrices to the diagonal of the scalar
exponentials. -/
theorem lieExp_generalLinearGroup_diagonal (v : n → ℝ) :
    ((lieExp
        ((unitsLieAlgebraEquiv (R := Matrix n n ℝ)).symm (Matrix.diagonal v)) :
          Matrix.GeneralLinearGroup n ℝ) : Matrix n n ℝ) =
      Matrix.diagonal (fun i => exp (v i)) := by
  rw [lieExp_generalLinearGroup_coe, Matrix.exp_diagonal]
  rw [Pi.exp_def]

/-- The abstract exponential on `GL(n, ℝ)`, expressed in matrices, commutes with transpose. -/
theorem lieExp_generalLinearGroup_transpose (A : Matrix n n ℝ) :
    ((lieExp
        ((unitsLieAlgebraEquiv (R := Matrix n n ℝ)).symm A.transpose) :
          Matrix.GeneralLinearGroup n ℝ) : Matrix n n ℝ) =
      (((lieExp
          ((unitsLieAlgebraEquiv (R := Matrix n n ℝ)).symm A) :
            Matrix.GeneralLinearGroup n ℝ) : Matrix n n ℝ)).transpose := by
  rw [lieExp_generalLinearGroup_coe, lieExp_generalLinearGroup_coe, Matrix.exp_transpose]

/-- The abstract exponential on `GL(n, ℝ)`, expressed in matrices, respects conjugation. -/
theorem lieExp_generalLinearGroup_conj
    (U : Matrix.GeneralLinearGroup n ℝ) (A : Matrix n n ℝ) :
    ((lieExp
        ((unitsLieAlgebraEquiv (R := Matrix n n ℝ)).symm (U * A * U⁻¹)) :
          Matrix.GeneralLinearGroup n ℝ) : Matrix n n ℝ) =
      U *
        ((lieExp
          ((unitsLieAlgebraEquiv (R := Matrix n n ℝ)).symm A) :
            Matrix.GeneralLinearGroup n ℝ) : Matrix n n ℝ) * U⁻¹ := by
  rw [lieExp_generalLinearGroup_coe, lieExp_generalLinearGroup_coe, Matrix.exp_units_conj]
