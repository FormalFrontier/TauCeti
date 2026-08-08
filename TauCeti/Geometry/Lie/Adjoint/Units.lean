/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Exponential
public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility

/-!
# The adjoint action on units of a normed algebra

For the Lie group of units of a finite-dimensional real normed algebra, the abstract adjoint
action is ordinary algebra conjugation. We obtain the formula by differentiating exponential
equivariance along a line, reusing the already established compatibility between the abstract
Lie-group exponential and the Banach-algebra exponential.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `unitsLieAlgebraEquiv_Ad`: under the canonical identification with the ambient algebra,
  `Ad g X` is `g * X * g⁻¹`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace TauCeti.Lie

attribute [local instance] TauCeti.normedAlgebraRatOfReal

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

local instance finiteDimensionalCompleteSpaceAdjointUnits : CompleteSpace R :=
  FiniteDimensional.complete ℝ R

/-- On the units of a finite-dimensional real normed algebra, the abstract group adjoint is
ordinary conjugation in the ambient algebra. -/
theorem unitsLieAlgebraEquiv_Ad (g : Rˣ)
    (X : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    unitsLieAlgebraEquiv (Ad (I := 𝓘(ℝ, R)) g X) =
      (g : R) * unitsLieAlgebraEquiv X * (g⁻¹ : Rˣ) := by
  let x : R := unitsLieAlgebraEquiv X
  let y : R := unitsLieAlgebraEquiv (Ad (I := 𝓘(ℝ, R)) g X)
  have hfun :
      (fun t : ℝ => (g : R) *
        (TauCeti.expUnitHom x (Multiplicative.ofAdd t) : R) * (g⁻¹ : Rˣ)) =
      fun t : ℝ => (TauCeti.expUnitHom y (Multiplicative.ofAdd t) : R) := by
    funext t
    have h := conj_lieExp (I := 𝓘(ℝ, R)) g (t • X)
    rw [lieExp_eq_expUnit, lieExp_eq_expUnit] at h
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val, TauCeti.expUnitHom_apply,
      x, y, map_smul] using congrArg Units.val h
  have hx := TauCeti.hasDerivAt_expUnitHom_val_zero x
  have hy := TauCeti.hasDerivAt_expUnitHom_val_zero y
  have hconj : HasDerivAt
      (fun t : ℝ => (g : R) *
        (TauCeti.expUnitHom x (Multiplicative.ofAdd t) : R) * (g⁻¹ : Rˣ))
      ((g : R) * x * (g⁻¹ : Rˣ)) 0 :=
    (HasDerivAt.const_mul (g : R) hx).mul_const (g⁻¹ : Rˣ)
  rw [hfun] at hconj
  exact hy.unique hconj

end TauCeti.Lie
