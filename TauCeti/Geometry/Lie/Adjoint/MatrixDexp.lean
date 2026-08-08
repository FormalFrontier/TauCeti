/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Geometry.Lie.Adjoint.BanachDexpDerivative

/-!
# The matrix dexp factor

For real square matrices, the regularized `dexp` factor is the integral of ordinary matrix
conjugations. This is the matrix shadow of the left-trivialized differential-of-exponential
factor.

## Main result

* `TauCeti.Lie.matrixDexpFactor_apply_eq_integral_conj`: the concrete matrix integral formula.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

noncomputable section

namespace TauCeti.Lie

open NormedSpace MeasureTheory
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix dexp factor is the integral of conjugation by the matrix exponential. -/
theorem matrixDexpFactor_apply_eq_integral_conj (A B : Matrix n n ℝ) :
    banachDexpFactor A B =
      ∫ t in (0 : ℝ)..1, exp ((-t) • A) * B * exp (t • A) :=
  banachDexpFactor_apply_eq_integral_conj A B

/-- The matrix-exponential derivative is left multiplication by `exp A` followed by the integral
of conjugations along the exponential line. -/
theorem matrixFDerivExp_apply_eq_integral_conj (A B : Matrix n n ℝ) :
    fderiv ℝ exp A B =
      exp A * (∫ t in (0 : ℝ)..1, exp ((-t) • A) * B * exp (t • A)) := by
  calc
    fderiv ℝ exp A B = expFDeriv ℝ A B := by
      exact congrArg
        (fun L : Matrix n n ℝ →L[ℝ] Matrix n n ℝ ↦ L B)
        (TauCeti.fderiv_exp (𝕂 := ℝ) A)
    _ = exp A * banachDexpFactor A B :=
      expFDeriv_apply_eq_exp_mul_banachDexpFactor A B
    _ = _ := by rw [matrixDexpFactor_apply_eq_integral_conj]

end TauCeti.Lie

