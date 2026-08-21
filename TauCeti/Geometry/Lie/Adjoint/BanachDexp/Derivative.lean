/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exponential
public import TauCeti.Geometry.Lie.Adjoint.BanachDexp.Integral
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# The closed form of the Banach-algebra exponential derivative

This file identifies the Fréchet derivative of the noncommutative exponential with the regularized
commutator quotient, followed by left multiplication by `exp x`.

## Main results

* `TauCeti.Lie.expFDeriv_apply_eq_exp_mul_banachDexpFactor`: the pointwise formula.
* `TauCeti.Lie.expFDeriv_eq_exp_mul_banachDexpFactor`: the bundled operator formula.
* `TauCeti.Lie.fderiv_exp_eq_exp_mul_banachDexpFactor`: the corresponding `fderiv` formula.
* `TauCeti.Lie.fderiv_exp_apply_eq_exp_mul_integral`: the pointwise integral formula.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

noncomputable section

namespace TauCeti.Lie

open NormedSpace MeasureTheory

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- The exponential derivative in direction `y` is left multiplication by `exp x` applied to
the regularized commutator factor. -/
theorem expFDeriv_apply_eq_exp_mul_banachDexpFactor {𝕂 : Type*}
    [NontriviallyNormedField 𝕂] [NormedAlgebra ℝ 𝕂] [NormedAlgebra 𝕂 R]
    [IsScalarTower ℝ 𝕂 R] (x y : R) :
    expFDeriv 𝕂 x y = exp x * banachDexpFactor x y := by
  rw [TauCeti.expFDeriv_apply_eq_integral,
    banachDexpFactor_apply_eq_integral]
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ exp (-(t • x)) * y * exp (t • x)) volume 0 1 := by
    exact Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 1
  rw [← ContinuousLinearMap.mul_apply' ℝ]
  rw [← (ContinuousLinearMap.mul ℝ R (exp x)).intervalIntegral_comp_comm hint]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [ContinuousLinearMap.mul_apply']
  have hcomm : Commute x (-(t • x)) := (Commute.refl x).smul_right t |>.neg_right
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

/-- The Fréchet derivative of the Banach-algebra exponential, applied to `y`, is left
multiplication by `exp x` applied to the integral of conjugations along the exponential line. -/
theorem fderiv_exp_apply_eq_exp_mul_integral {𝕂 : Type*}
    [NontriviallyNormedField 𝕂] [NormedAlgebra ℝ 𝕂] [NormedAlgebra 𝕂 R]
    [IsScalarTower ℝ 𝕂 R] (x y : R) :
    fderiv 𝕂 exp x y =
      exp x * (∫ t in (0 : ℝ)..1, exp (-(t • x)) * y * exp (t • x)) := by
  let _ : CharZero 𝕂 := Algebra.charZero_of_charZero ℝ 𝕂
  let _ : IsScalarTower ℚ ℝ 𝕂 := IsScalarTower.of_algebraMap_eq fun q ↦ by simp [map_ratCast]
  let _ : ContinuousSMul ℚ 𝕂 := IsScalarTower.continuousSMul ℝ
  rw [TauCeti.fderiv_exp, expFDeriv_apply_eq_exp_mul_banachDexpFactor,
    banachDexpFactor_apply_eq_integral]

end TauCeti.Lie
