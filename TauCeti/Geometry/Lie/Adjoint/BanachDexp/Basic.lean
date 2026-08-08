/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.OperatorExponential
public import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Basic

/-!
# The Banach-algebra dexp factor

This file evaluates the regularized exponential quotient at the bounded commutator operator. The
result is the Banach-algebra realization of `(1 - exp (-ad x)) / ad x`, the left-trivialized
factor in the differential of a Lie-group exponential.

## Main definitions

* `TauCeti.Lie.banachDexpFactor`: the regularized quotient at the bounded commutator.

## Main results

* `TauCeti.Lie.continuousCommutator_mul_banachDexpFactor`: the operator quotient identity.
* `TauCeti.Lie.banachDexpFactor_mul_continuousCommutator`: the symmetric quotient identity.
* `TauCeti.Lie.commute_continuousCommutator_banachDexpFactor`: the factor commutes with `ad x`.
* `TauCeti.Lie.continuousCommutator_banachDexpFactor_apply`: its concrete conjugation form.
* `TauCeti.Lie.banachDexpFactor_continuousCommutator_apply`: the symmetric pointwise form.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

noncomputable section

namespace TauCeti.Lie

open NormedSpace

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- The Banach-algebra realization of the regularized operator quotient
`(1 - exp (-ad x)) / ad x`. -/
noncomputable def banachDexpFactor (x : R) : R →L[ℝ] R :=
  oneSubExpNegDivSelf ℝ (continuousCommutator x)

omit [CompleteSpace R] in
/-- The Banach dexp factor is the regularized quotient evaluated at the commutator operator. -/
theorem banachDexpFactor_eq_oneSubExpNegDivSelf (x : R) :
    banachDexpFactor x = oneSubExpNegDivSelf ℝ (continuousCommutator x) := by
  rw [banachDexpFactor]

omit [CompleteSpace R] in
/-- At zero, the Banach-algebra dexp factor is the identity operator. -/
@[simp]
theorem banachDexpFactor_zero : banachDexpFactor (0 : R) = 1 := by
  rw [banachDexpFactor_eq_oneSubExpNegDivSelf, map_zero, oneSubExpNegDivSelf_zero]

/-- Multiplication by the commutator operator cancels the regularized denominator. -/
@[simp]
theorem continuousCommutator_mul_banachDexpFactor (x : R) :
    continuousCommutator x * banachDexpFactor x =
      1 - exp (-continuousCommutator x) := by
  rw [banachDexpFactor_eq_oneSubExpNegDivSelf, mul_oneSubExpNegDivSelf]

/-- Multiplication by the commutator operator on the right also cancels the regularized
denominator. -/
@[simp]
theorem banachDexpFactor_mul_continuousCommutator (x : R) :
    banachDexpFactor x * continuousCommutator x =
      1 - exp (-continuousCommutator x) := by
  rw [banachDexpFactor_eq_oneSubExpNegDivSelf, oneSubExpNegDivSelf_mul]

omit [CompleteSpace R] in
/-- The commutator operator commutes with its Banach dexp factor. -/
theorem commute_continuousCommutator_banachDexpFactor (x : R) :
    Commute (continuousCommutator x) (banachDexpFactor x) := by
  rw [banachDexpFactor_eq_oneSubExpNegDivSelf]
  exact commute_oneSubExpNegDivSelf (continuousCommutator x)

/-- The operator quotient identity evaluated on an algebra element, with the operator exponential
rewritten as concrete conjugation. -/
theorem continuousCommutator_banachDexpFactor_apply (x y : R) :
    continuousCommutator x (banachDexpFactor x y) =
      y - exp (-x) * y * exp x := by
  have hneg : -continuousCommutator x = continuousCommutator (-x) :=
    (map_neg continuousCommutator x).symm
  have h := congrArg (fun f : R →L[ℝ] R ↦ f y)
    (continuousCommutator_mul_banachDexpFactor x)
  simpa only [mul_apply_eq_comp, one_apply_eq_self, sub_apply, hneg,
    exp_continuousCommutator_apply, neg_neg] using h

/-- The symmetric operator quotient identity evaluated on an algebra element, with the operator
exponential rewritten as concrete conjugation. -/
theorem banachDexpFactor_continuousCommutator_apply (x y : R) :
    banachDexpFactor x (continuousCommutator x y) =
      y - exp (-x) * y * exp x := by
  rw [← mul_apply_eq_comp,
    ← (commute_continuousCommutator_banachDexpFactor x).eq, mul_apply_eq_comp]
  exact continuousCommutator_banachDexpFactor_apply x y

end TauCeti.Lie
