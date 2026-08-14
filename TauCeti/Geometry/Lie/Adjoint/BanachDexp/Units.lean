/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.BanachDexp.Derivative
public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility

/-!
# The differential of the exponential on a finite-dimensional algebra's units

After coercing the units-valued Lie exponential to the ambient algebra, its Fréchet derivative
is left multiplication by the exponential composed with the regularized commutator factor and
the canonical identification of the abstract Lie algebra with the ambient algebra.

## Main result

* `TauCeti.Lie.fderiv_lieExp_units_coe_eq_exp_mul_banachDexpFactor`: the bundled derivative formula.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

open Manifold NormedSpace
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Lie

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

local instance finiteDimensionalCompleteSpaceUnitsDexp : CompleteSpace R :=
  FiniteDimensional.complete ℝ R

attribute [local instance] TauCeti.normedAlgebraRatOfReal

local instance finiteDimensionalLeftInvariantDerivationUnitsDexp :
    FiniteDimensional ℝ (LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

/-- The derivative of the units Lie exponential after coercion to the ambient algebra is left
multiplication by the exponential composed with the regularized commutator factor and the
canonical Lie-algebra equivalence. -/
theorem fderiv_lieExp_units_coe_eq_exp_mul_banachDexpFactor
    (X : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    fderiv ℝ
        (fun Y : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ =>
          ((lieExp (I := 𝓘(ℝ, R)) (G := Rˣ) Y : Rˣ) : R)) X =
      (ContinuousLinearMap.mul ℝ R (exp (unitsLieAlgebraEquiv X))).comp
        ((banachDexpFactor (unitsLieAlgebraEquiv X)).comp
          (unitsLieAlgebraEquiv (R := R)).toContinuousLinearEquiv.toContinuousLinearMap) := by
  have hfun : (fun Y : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ =>
      ((lieExp (I := 𝓘(ℝ, R)) (G := Rˣ) Y : Rˣ) : R)) =
      exp ∘ unitsLieAlgebraEquiv (R := R) := by
    funext Y
    rw [lieExp_eq_expUnit, TauCeti.expUnit_coe]
    rfl
  rw [hfun]
  rw [fderiv_comp X (TauCeti.hasFDerivAt_exp (unitsLieAlgebraEquiv X)).differentiableAt
    (unitsLieAlgebraEquiv (R := R)).toContinuousLinearEquiv.differentiableAt,
    fderiv_exp_eq_exp_mul_banachDexpFactor]
  have he : fderiv ℝ (unitsLieAlgebraEquiv (R := R)) X =
      (unitsLieAlgebraEquiv (R := R)).toContinuousLinearEquiv.toContinuousLinearMap :=
    (unitsLieAlgebraEquiv (R := R)).toContinuousLinearEquiv.hasFDerivAt.fderiv
  rw [he]
  exact ContinuousLinearMap.comp_assoc _ _ _

end TauCeti.Lie
