/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic
public import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Compatibility of the abstract and Banach-algebra exponentials

The abstract Lie-group exponential recovers the Banach-algebra exponential on the Lie group `Rˣ`.
Under the canonical identification of its tangent Lie algebra with `R`, the generated abstract
one-parameter subgroup is `TauCeti.expUnitHom`, and its time-one value is `TauCeti.expUnit`.

## Main results

* `unitsGroupLieAlgebraEquiv`: the tangent Lie algebra of `Rˣ` is canonically `R`.
* `hasDerivAt_mulInvariantOneParameterSubgroup_val_zero`: the abstract invariant subgroup has the
  expected velocity in the units chart.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The matrix and circle shadows".
-/

public section

open Manifold
open scoped ContDiff Manifold

noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- A real normed algebra regarded as a rational normed algebra within this module. -/
noncomputable local instance normedAlgebraRatOfReal : NormedAlgebra ℚ R :=
  NormedAlgebra.restrictScalars ℚ ℝ R

/-- The tangent Lie algebra of the units of a normed real algebra is its model space. -/
noncomputable def unitsGroupLieAlgebraEquiv :
    GroupLieAlgebra 𝓘(ℝ, R) Rˣ ≃ₗ[ℝ] R :=
  LinearEquiv.refl ℝ R

/-- The canonical invariant one-parameter subgroup on `Rˣ` with tangent vector `x` has initial
velocity `x` after embedding the units in `R`. -/
theorem hasDerivAt_mulInvariantOneParameterSubgroup_val_zero (x : R) :
    HasDerivAt
      (fun t : ℝ =>
        (mulInvariantOneParameterSubgroup (unitsGroupLieAlgebraEquiv.symm x)
          (Multiplicative.ofAdd t) : R)) x 0 := by
  let v : GroupLieAlgebra 𝓘(ℝ, R) Rˣ := x
  have hv : unitsGroupLieAlgebraEquiv.symm x = v := by
    rfl
  have hfun :
      (fun t : ℝ =>
        (mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd t) : R)) =
        fun t : ℝ =>
          (mulInvariantIntegralCurve (I := 𝓘(ℝ, R)) (G := Rˣ) v (1 : Rˣ) t : R) := by
    funext t
    exact congrArg Units.val
      (mulInvariantOneParameterSubgroup_apply (I := 𝓘(ℝ, R)) (G := Rˣ) v t)
  have h := (isMIntegralCurve_mulInvariantIntegralCurve (I := 𝓘(ℝ, R)) (G := Rˣ)
    v (1 : Rˣ)).isMIntegralCurveAt 0
  have hd := h.eventually_hasDerivAt.self_of_nhds
  have hzero : mulInvariantIntegralCurve (I := 𝓘(ℝ, R)) (G := Rˣ) v 1 0 = 1 :=
    mulInvariantIntegralCurve_zero v 1
  rw [hzero] at hd
  have hone : (1 : Rˣ) ∈ (extChartAt 𝓘(ℝ, R) (1 : Rˣ)).source :=
    mem_of_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ, R)) (1 : Rˣ))
  rw [mulInvariantVectorField_one] at hd
  dsimp only [v] at hd
  rw [tangentCoordChange_self hone] at hd
  -- The preferred chart on the open submanifold `Rˣ` is its value map into `R`.
  change HasDerivAt
    (fun t : ℝ => (mulInvariantIntegralCurve (I := 𝓘(ℝ, R)) (G := Rˣ) v 1 t : R)) x 0 at hd
  rw [hv]
  rw [hfun]
  exact hd
