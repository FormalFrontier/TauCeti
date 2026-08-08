/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exponential
public import TauCeti.Geometry.Lie.Adjoint.BanachDexpIntegral

/-!
# The closed form of the Banach-algebra exponential derivative

This file identifies the Fréchet derivative of the noncommutative exponential with left
multiplication by `exp x`, followed by the regularized commutator quotient.

## Main results

* `TauCeti.Lie.expFDeriv_apply_eq_exp_mul_banachDexpFactor`: the pointwise formula.
* `TauCeti.Lie.expFDeriv_eq_exp_mul_banachDexpFactor`: the bundled operator formula.
* `TauCeti.Lie.fderiv_exp_eq_exp_mul_banachDexpFactor`: the corresponding `fderiv` formula.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

noncomputable section

namespace TauCeti.Lie

open NormedSpace MeasureTheory

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- A real normed algebra regarded as a rational normed algebra within this module. -/
noncomputable local instance normedAlgebraRatOfRealBanachDexpDerivative : NormedAlgebra ℚ R :=
  .restrictScalars ℚ ℝ R

/-- The exponential derivative in direction `y` is left multiplication by `exp x` applied to
the regularized commutator factor. -/
theorem expFDeriv_apply_eq_exp_mul_banachDexpFactor (x y : R) :
    expFDeriv ℝ x y = exp x * banachDexpFactor x y := by
  rw [TauCeti.expFDeriv_apply_eq_integral,
    banachDexpFactor_apply_eq_integral_conj]
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ exp ((-t) • x) * y * exp (t • x)) volume 0 1 := by
    exact Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 1
  change (∫ t in (0 : ℝ)..1, exp ((1 - t) • x) * y * exp (t • x)) =
    (ContinuousLinearMap.mul ℝ R (exp x))
      (∫ t in (0 : ℝ)..1, exp ((-t) • x) * y * exp (t • x))
  rw [← (ContinuousLinearMap.mul ℝ R (exp x)).intervalIntegral_comp_comm hint]
  apply intervalIntegral.integral_congr
  intro t _ht
  change exp ((1 - t) • x) * y * exp (t • x) =
    exp x * (exp ((-t) • x) * y * exp (t • x))
  have hcomm : Commute x ((-t) • x) := (Commute.refl x).smul_right (-t)
  rw [← mul_assoc, ← mul_assoc, ← exp_add_of_commute hcomm]
  congr 3
  module

/-- The Fréchet derivative is left multiplication by `exp x` composed with the regularized
commutator factor. -/
theorem expFDeriv_eq_exp_mul_banachDexpFactor (x : R) :
    expFDeriv ℝ x =
      (ContinuousLinearMap.mul ℝ R (exp x)).comp (banachDexpFactor x) := by
  ext y
  exact expFDeriv_apply_eq_exp_mul_banachDexpFactor x y

/-- The Fréchet derivative of the Banach-algebra exponential is left multiplication by `exp x`
composed with `(1 - exp (-ad x)) / ad x`. -/
theorem fderiv_exp_eq_exp_mul_banachDexpFactor (x : R) :
    fderiv ℝ exp x =
      (ContinuousLinearMap.mul ℝ R (exp x)).comp (banachDexpFactor x) := by
  rw [TauCeti.fderiv_exp, expFDeriv_eq_exp_mul_banachDexpFactor]

end TauCeti.Lie

