/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.IntegralCurve

/-!
# The exponential map of a Lie group

This file defines the tangent-space exponential of a finite-dimensional real Lie group by
evaluating the canonical invariant one-parameter subgroup at time one.

## Main results

* `mulInvariantExp`: the time-one value of the invariant curve attached to a tangent vector.
* `mulInvariantExp_smul`: scaling a tangent vector is evaluation at the corresponding time.
* `mulInvariantExp_add_smul`: the exponential along a fixed line is a one-parameter subgroup.
* `mulInvariantExp_zero`: the exponential sends zero to the group identity.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open Function Manifold VectorField
open scoped Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- The tangent-space exponential obtained by evaluating the canonical invariant curve at time
one. This is the tangent-vector precursor of the roadmap's derivation-based `lieExp`. -/
noncomputable def mulInvariantExp [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) : G :=
  mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd 1)

/-- Scaling a tangent vector corresponds to evaluating its invariant integral curve at the scale
factor. -/
theorem mulInvariantExp_smul [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (t : ℝ) :
    mulInvariantExp (t • v) = mulInvariantIntegralCurve v 1 t := by
  let γ := mulInvariantIntegralCurve v 1
  have hscaled : IsMIntegralCurve (γ ∘ (· * t)) (mulInvariantVectorField (t • v)) := by
    rw [mulInvariantVectorField_smul]
    exact (isMIntegralCurve_mulInvariantIntegralCurve v 1).comp_mul t
  have heq : γ ∘ (· * t) = mulInvariantIntegralCurve (t • v) 1 := by
    apply eq_mulInvariantIntegralCurve (t • v) 1
    · simp [γ]
    · exact hscaled
  rw [mulInvariantExp, mulInvariantOneParameterSubgroup_apply]
  simpa [γ] using (congrFun heq 1).symm

/-- The exponential along a line satisfies the one-parameter subgroup law. -/
@[simp]
theorem mulInvariantExp_add_smul [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (s t : ℝ) :
    mulInvariantExp ((s + t) • v) = mulInvariantExp (s • v) * mulInvariantExp (t • v) := by
  rw [mulInvariantExp_smul, mulInvariantExp_smul, mulInvariantExp_smul,
    mulInvariantIntegralCurve_add]

/-- The tangent-space exponential sends zero to the group identity. -/
@[simp]
theorem mulInvariantExp_zero [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] : mulInvariantExp (0 : GroupLieAlgebra I G) = 1 := by
  simpa using mulInvariantExp_smul (0 : GroupLieAlgebra I G) 0
