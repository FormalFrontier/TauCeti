/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Exponentiating the commutator operator

In a real Banach algebra, exponentiating the continuous commutator operator
`y ↦ x * y - y * x` gives conjugation by `exp x`. This is the Banach-algebra shadow of the Lie-group
identity `Ad (lieExp X) = exp (ad X)`. The final result identifies the underlying linear map of the
bounded commutator with Mathlib's `LieAlgebra.ad` for the associative-ring Lie bracket.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `TauCeti.Lie.continuousCommutator`: the continuous commutator operator associated to an algebra
  element.

## Main results

* `TauCeti.Lie.exp_mulLeft_apply`: exponentiating left multiplication acts by `exp x` on the left.
* `TauCeti.Lie.exp_mulRight_apply`: the analogous right-multiplication identity.
* `TauCeti.Lie.exp_continuousCommutator_apply`: its operator exponential acts by conjugation.
* `TauCeti.Lie.exp_continuousCommutator`: the corresponding equality of bounded operators.
* `TauCeti.Lie.continuousCommutator_toLinearMap`: its underlying linear map is Mathlib's
  `LieAlgebra.ad`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

noncomputable section

namespace TauCeti.Lie

open NormedSpace

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- The rational scalar restriction used by Mathlib's exponential API in this module. -/
noncomputable local instance normedAlgebraRat : NormedAlgebra ℚ R :=
  .restrictScalars ℚ ℝ R

omit [CompleteSpace R] in
private theorem mulLeft_pow_apply (x y : R) (n : ℕ) :
    ((ContinuousLinearMap.mul ℝ R x) ^ n) y = x ^ n * y := by
  -- Transport Mathlib's linear-map power identity through the underlying linear map.
  change (((ContinuousLinearMap.mul ℝ R x) ^ n).toLinearMap) y = x ^ n * y
  rw [ContinuousLinearMap.toLinearMap_pow]
  exact LinearMap.congr_fun (LinearMap.pow_mulLeft ℝ R x n) y

omit [CompleteSpace R] in
private theorem mulRight_pow_apply (x y : R) (n : ℕ) :
    (((ContinuousLinearMap.mul ℝ R).flip x) ^ n) y = y * x ^ n := by
  -- Transport Mathlib's linear-map power identity through the underlying linear map.
  change ((((ContinuousLinearMap.mul ℝ R).flip x) ^ n).toLinearMap) y = y * x ^ n
  rw [ContinuousLinearMap.toLinearMap_pow]
  exact LinearMap.congr_fun (LinearMap.pow_mulRight ℝ R x n) y

/-- Exponentiating the bounded left-multiplication operator gives left multiplication by the
algebra exponential. -/
theorem exp_mulLeft_apply (x y : R) :
    exp (ContinuousLinearMap.mul ℝ R x) y = exp x * y := by
  have hop := (ContinuousLinearMap.apply ℝ R y).hasSum
    (exp_series_hasSum_exp' (𝕂 := ℝ) (ContinuousLinearMap.mul ℝ R x))
  have halg := (exp_series_hasSum_exp' (𝕂 := ℝ) x).mul_right y
  apply HasSum.unique (hop.congr fun n => ?_) halg
  simp only [map_smul, ContinuousLinearMap.apply_apply, mulLeft_pow_apply]
  simp only [smul_mul_assoc]

/-- Exponentiating the bounded right-multiplication operator gives right multiplication by the
algebra exponential. -/
theorem exp_mulRight_apply (x y : R) :
    exp ((ContinuousLinearMap.mul ℝ R).flip x) y = y * exp x := by
  have hop := (ContinuousLinearMap.apply ℝ R y).hasSum
    (exp_series_hasSum_exp' (𝕂 := ℝ) ((ContinuousLinearMap.mul ℝ R).flip x))
  have halg := (exp_series_hasSum_exp' (𝕂 := ℝ) x).mul_left y
  apply HasSum.unique (hop.congr fun n => ?_) halg
  simp only [map_smul, ContinuousLinearMap.apply_apply, mulRight_pow_apply]
  simp only [mul_smul_comm]

/-- The continuous-linear family of endomorphisms `y ↦ x * y - y * x`. -/
def continuousCommutator : R →L[ℝ] R →L[ℝ] R :=
  ContinuousLinearMap.mul ℝ R - (ContinuousLinearMap.mul ℝ R).flip

omit [CompleteSpace R] in
@[simp]
theorem continuousCommutator_apply (x y : R) :
    continuousCommutator x y = x * y - y * x := by
  simp [continuousCommutator]

/-- Exponentiating the continuous commutator operator gives conjugation by the algebra
exponential. -/
@[simp]
theorem exp_continuousCommutator_apply (x y : R) :
    exp (continuousCommutator x) y = exp x * y * exp (-x) := by
  let L := ContinuousLinearMap.mul ℝ R x
  let R' := (ContinuousLinearMap.mul ℝ R).flip x
  have hcomm : Commute L R' := by
    apply ContinuousLinearMap.ext
    intro z
    exact LinearMap.congr_fun (LinearMap.commute_mulLeft_right x x).eq z
  have hcommutator : continuousCommutator x = L - R' := rfl
  rw [hcommutator, sub_eq_add_neg, exp_add_of_commute hcomm.neg_right,
    mul_apply_eq_comp]
  have hneg : -R' = (ContinuousLinearMap.mul ℝ R).flip (-x) := by
    simpa only [R'] using (map_neg (ContinuousLinearMap.mul ℝ R).flip x).symm
  rw [hneg, exp_mulRight_apply, exp_mulLeft_apply, mul_assoc]

/-- Exponentiating the continuous commutator gives the bounded conjugation operator. -/
theorem exp_continuousCommutator (x : R) :
    exp (continuousCommutator x) =
      ContinuousLinearMap.mulLeftRight ℝ R (exp x) (exp (-x)) := by
  ext y
  simp

section AlgebraicAdjoint

attribute [local instance 100] LieRing.ofAssociativeRing

omit [CompleteSpace R] in
/-- The continuous commutator is the bounded realization of Mathlib's algebraic adjoint map for
the ring-commutator bracket supplied by `LieRing.ofAssociativeRing`. Callers who restate the
right-hand side should enable that instance locally. -/
theorem continuousCommutator_toLinearMap (x : R) :
    (continuousCommutator x).toLinearMap = LieAlgebra.ad ℝ R x := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  ext y
  simp [continuousCommutator]

end AlgebraicAdjoint

end TauCeti.Lie
