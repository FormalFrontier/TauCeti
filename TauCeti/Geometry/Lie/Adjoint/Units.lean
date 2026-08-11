/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Exponential
public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility

/-!
# The adjoint action on units of a normed algebra

For the Lie group of units of a complete real normed algebra, the tangent adjoint action is
ordinary algebra conjugation. In finite dimensions, the same formula describes the adjoint on
left-invariant derivations under the canonical identification with the ambient algebra. We obtain
the tangent formula by differentiating exponential equivariance along a line, reusing the already
established compatibility between the abstract Lie-group exponential and the Banach-algebra
exponential.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `tangentAd_units`: on the tangent Lie algebra of the unit group, `tangentAd g x` is
  `g * x * g⁻¹`.
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

section Complete

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- On the units of a complete real normed algebra, the tangent adjoint is ordinary conjugation
in the ambient algebra. -/
@[simp high]
theorem tangentAd_units (g : Rˣ) (x : R) :
    tangentAd (I := 𝓘(ℝ, R)) g (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) =
      (g : R) * x * ((g⁻¹ : Rˣ) : R) := by
  let y : R := tangentAd (I := 𝓘(ℝ, R)) g (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
  have hfun :
      (fun t : ℝ => (g : R) *
        (TauCeti.expUnitHom x (Multiplicative.ofAdd t) : R) * ((g⁻¹ : Rˣ) : R)) =
      fun t : ℝ => (TauCeti.expUnitHom y (Multiplicative.ofAdd t) : R) := by
    funext t
    have h := conj_mulInvariantIntegralCurve (I := 𝓘(ℝ, R)) g
      (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) (1 : Rˣ) t
    dsimp only at h
    simp only [mul_one, mul_inv_cancel] at h
    rw [← mulInvariantOneParameterSubgroup_apply
      (I := 𝓘(ℝ, R)) (G := Rˣ) (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) t] at h
    rw [← mulInvariantOneParameterSubgroup_apply
      (I := 𝓘(ℝ, R)) (G := Rˣ)
        (tangentAd (I := 𝓘(ℝ, R)) g (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)) t] at h
    -- The unit group's Lie algebra is definitionally its model space `R`; expose that
    -- identification so the bundled subgroup equalities can rewrite both sides.
    change g * mulInvariantOneParameterSubgroup
      (I := 𝓘(ℝ, R)) (G := Rˣ) (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
        (Multiplicative.ofAdd t) * g⁻¹ =
      mulInvariantOneParameterSubgroup
        (I := 𝓘(ℝ, R)) (G := Rˣ) (y : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
          (Multiplicative.ofAdd t) at h
    rw [mulInvariantOneParameterSubgroup_eq_expUnitHom,
      mulInvariantOneParameterSubgroup_eq_expUnitHom] at h
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val, y] using congrArg Units.val h
  have hx := TauCeti.hasDerivAt_expUnitHom_val_zero x
  have hy := TauCeti.hasDerivAt_expUnitHom_val_zero y
  have hconj : HasDerivAt
      (fun t : ℝ => (g : R) *
        (TauCeti.expUnitHom x (Multiplicative.ofAdd t) : R) * ((g⁻¹ : Rˣ) : R))
      ((g : R) * x * ((g⁻¹ : Rˣ) : R)) 0 :=
    (HasDerivAt.const_mul (g : R) hx).mul_const (g⁻¹ : Rˣ)
  rw [hfun] at hconj
  exact hy.unique hconj

end Complete

section FiniteDimensional

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

local instance finiteDimensionalCompleteSpaceAdjointUnits : CompleteSpace R :=
  FiniteDimensional.complete ℝ R

/-- On the units of a finite-dimensional real normed algebra, the abstract group adjoint is
ordinary conjugation in the ambient algebra. -/
@[simp high]
theorem unitsLieAlgebraEquiv_Ad (g : Rˣ)
    (X : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    unitsLieAlgebraEquiv (Ad (I := 𝓘(ℝ, R)) g X) =
      (g : R) * unitsLieAlgebraEquiv X * (g⁻¹ : Rˣ) := by
  have h := leftInvariantDerivationLieEquivGroupLieAlgebra_Ad
    (I := 𝓘(ℝ, R)) g X
  -- Expose the same definitional identification with `R` to compare the general tangent-space
  -- transport theorem with the units-specific equivalence.
  have hR := congrArg
    (fun x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ ↦ show R from x) h
  have ht := tangentAd_units (R := R) g
    (show R from leftInvariantDerivationLieEquivGroupLieAlgebra
      (I := 𝓘(ℝ, R)) (G := Rˣ)
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, R)) (n := ∞) (by simp) (1 : Rˣ)) X)
  rw [ht] at hR
  simpa only [unitsLieAlgebraEquiv_apply,
    leftInvariantDerivationLieEquivGroupLieAlgebra_apply] using hR

end FiniteDimensional

end TauCeti.Lie
