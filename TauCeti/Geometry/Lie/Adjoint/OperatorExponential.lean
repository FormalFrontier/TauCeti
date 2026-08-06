/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Geometry.Lie.Exponential.Units.Basic

/-!
# Exponentiating the commutator operator

In a real Banach algebra, exponentiating the continuous commutator operator
`y ↦ x * y - y * x` gives conjugation by `exp x`. This is the Banach-algebra shadow of the Lie-group
identity `Ad (lieExp X) = exp (ad X)`.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `TauCeti.Lie.continuousCommutator`: the continuous commutator operator associated to an algebra
  element.

## Main results

* `TauCeti.Lie.exp_continuousCommutator_apply`: its operator exponential acts by conjugation.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

noncomputable section

namespace TauCeti.Lie

open NormedSpace

attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

private def mulLeft (x : R) : R →L[ℝ] R :=
  ContinuousLinearMap.mul ℝ R x

private def mulRight (x : R) : R →L[ℝ] R :=
  (ContinuousLinearMap.mul ℝ R).flip x

omit [CompleteSpace R] in
private theorem mulLeft_apply (x y : R) : mulLeft x y = x * y :=
  rfl

omit [CompleteSpace R] in
private theorem mulRight_apply (x y : R) : mulRight x y = y * x :=
  rfl

omit [CompleteSpace R] in
private theorem mulLeft_pow_apply (x y : R) (n : ℕ) :
    (mulLeft x ^ n) y = x ^ n * y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      simp only [mul_apply_eq_comp, mulLeft_apply, ih,
        mul_assoc]

omit [CompleteSpace R] in
private theorem mulRight_pow_apply (x y : R) (n : ℕ) :
    (mulRight x ^ n) y = y * x ^ n := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ']
      simp only [mul_apply_eq_comp, mulRight_apply, ih,
        mul_assoc]

private theorem exp_mulLeft_apply (x y : R) :
    exp (mulLeft x) y = exp x * y := by
  have hop := (ContinuousLinearMap.apply ℝ R y).hasSum
    (exp_series_hasSum_exp' (𝕂 := ℝ) (mulLeft x))
  have halg := (exp_series_hasSum_exp' (𝕂 := ℝ) x).mul_right y
  apply HasSum.unique (hop.congr fun n => ?_) halg
  simp only [map_smul, ContinuousLinearMap.apply_apply, mulLeft_pow_apply]
  simp only [smul_mul_assoc]

private theorem exp_mulRight_apply (x y : R) :
    exp (mulRight x) y = y * exp x := by
  have hop := (ContinuousLinearMap.apply ℝ R y).hasSum
    (exp_series_hasSum_exp' (𝕂 := ℝ) (mulRight x))
  have halg := (exp_series_hasSum_exp' (𝕂 := ℝ) x).mul_left y
  apply HasSum.unique (hop.congr fun n => ?_) halg
  simp only [map_smul, ContinuousLinearMap.apply_apply, mulRight_pow_apply]
  simp only [mul_smul_comm]

/-- The continuous endomorphism `y ↦ x * y - y * x`. -/
def continuousCommutator (x : R) : R →L[ℝ] R :=
  mulLeft x - mulRight x

omit [CompleteSpace R] in
@[simp]
theorem continuousCommutator_apply (x y : R) :
    continuousCommutator x y = x * y - y * x := by
  rw [continuousCommutator]
  rfl

/-- Exponentiating the continuous commutator operator gives conjugation by the algebra
exponential. -/
theorem exp_continuousCommutator_apply (x y : R) :
    exp (continuousCommutator x) y = exp x * y * exp (-x) := by
  have hcomm : Commute (mulLeft x) (-mulRight x) := by
    rw [Commute]
    ext z
    simp only [mul_apply_eq_comp, neg_apply, mulLeft_apply,
      mulRight_apply]
    simp [mul_assoc]
  rw [continuousCommutator, sub_eq_add_neg, exp_add_of_commute hcomm]
  change exp (mulLeft x) (exp (-mulRight x) y) = _
  have hneg : -mulRight x = mulRight (-x) := by
    ext z
    simp [mulRight_apply]
  rw [hneg, exp_mulRight_apply, exp_mulLeft_apply, mul_assoc]

section AlgebraicAdjoint

attribute [local instance 100] LieRing.ofAssociativeRing

omit [CompleteSpace R] in
/-- The continuous commutator is the bounded realization of Mathlib's algebraic adjoint map. -/
theorem continuousCommutator_toLinearMap (x : R) :
    (continuousCommutator x).toLinearMap = LieAlgebra.ad ℝ R x := by
  ext y
  change continuousCommutator x y = LieAlgebra.ad ℝ R x y
  rw [continuousCommutator_apply, LieAlgebra.ad_apply,
    LieRing.of_associative_ring_bracket]

end AlgebraicAdjoint

end TauCeti.Lie
