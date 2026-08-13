/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.BanachDexp.Units
public import TauCeti.Geometry.Lie.Exponential.Matrix.Compatibility

/-!
# The differential of the general-linear-group exponential in matrix coordinates

After identifying the Lie algebra of `GL(n, ℝ)` with square matrices and coercing the group-valued
exponential back to matrices, its derivative is left multiplication by `exp A` applied to the
integral of conjugations along the exponential line. The statements use Mathlib's scoped `L∞`
operator norm on matrices; in finite dimension this does not change the derivative or topology.

## Main result

* `fderiv_lieExp_generalLinearGroup_coe_eq_exp_mul_banachDexpFactor`: the bundled derivative of
  the abstract Lie-group exponential in matrix coordinates.
* `fderiv_lieExp_generalLinearGroup_coe_apply_eq_exp_mul_integral`: its pointwise integral formula.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

noncomputable section

open NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace TauCeti.Lie

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- In matrix coordinates, the derivative of the abstract exponential on `GL(n, ℝ)` is left
multiplication by the matrix exponential composed with the regularized commutator factor. -/
theorem fderiv_lieExp_generalLinearGroup_coe_eq_exp_mul_banachDexpFactor (A : Matrix n n ℝ) :
    fderiv ℝ
        (fun C : Matrix n n ℝ =>
          ((lieExp
              ((unitsLieAlgebraEquiv (R := Matrix n n ℝ)).symm C) :
                Matrix.GeneralLinearGroup n ℝ) : Matrix n n ℝ)) A =
      (ContinuousLinearMap.mul ℝ (Matrix n n ℝ) (exp A)).comp
        (banachDexpFactor A) := by
  have hfun :
      (fun C : Matrix n n ℝ =>
        ((lieExp
            ((unitsLieAlgebraEquiv (R := Matrix n n ℝ)).symm C) :
              Matrix.GeneralLinearGroup n ℝ) : Matrix n n ℝ)) = exp := by
    funext C
    exact lieExp_generalLinearGroup_coe C
  rw [hfun]
  exact fderiv_exp_eq_exp_mul_banachDexpFactor A

/-- In matrix coordinates, the derivative of the abstract exponential on `GL(n, ℝ)` is left
multiplication by `exp A` applied to the integral of conjugations along the exponential line. -/
theorem fderiv_lieExp_generalLinearGroup_coe_apply_eq_exp_mul_integral (A B : Matrix n n ℝ) :
    fderiv ℝ
        (fun C : Matrix n n ℝ =>
          ((lieExp
              ((unitsLieAlgebraEquiv (R := Matrix n n ℝ)).symm C) :
                Matrix.GeneralLinearGroup n ℝ) : Matrix n n ℝ)) A B =
      exp A * (∫ t in (0 : ℝ)..1, exp (-(t • A)) * B * exp (t • A)) := by
  rw [fderiv_lieExp_generalLinearGroup_coe_eq_exp_mul_banachDexpFactor]
  change exp A * banachDexpFactor A B = _
  rw [banachDexpFactor_apply_eq_integral]
  rfl

end TauCeti.Lie
