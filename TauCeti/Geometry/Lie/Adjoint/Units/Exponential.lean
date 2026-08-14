/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Units.Basic

/-!
# Exponential compatibility of the adjoint action on algebra units

For the Lie group of units of a complete real normed algebra, the tangent adjoint of an exponential
is the exponential of the continuous commutator operator. In finite dimensions, this transports to
the abstract identity `Ad (lieExp X) = exp (ad X)` on left-invariant derivations.

## Main result

* `tangentAd_expUnit`: the tangent adjoint of an algebra-unit exponential is the exponential of the
  continuous commutator.
* `Ad_lieExp_units`: the finite-dimensional identity `Ad (lieExp X) = exp (ad X)` on
  left-invariant derivations.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

noncomputable section

open Manifold NormedSpace
open scoped ContDiff Manifold

namespace TauCeti.Lie

attribute [local instance] TauCeti.normedAlgebraRatOfReal

section Complete

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- On algebra units, the tangent adjoint of an exponential is the exponential of the continuous
commutator by its exponent. -/
theorem tangentAd_expUnit (x y : R) :
    tangentAd (I := 𝓘(ℝ, R)) (TauCeti.expUnit x)
        (y : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) =
      exp (continuousCommutator x) y := by
  rw [tangentAd_units, exp_continuousCommutator_apply,
    ← TauCeti.expUnit_neg]
  simp only [TauCeti.expUnit_coe]
  rfl

end Complete

section FiniteDimensional

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

local instance finiteDimensionalCompleteSpaceAdjointUnitsExponential : CompleteSpace R :=
  FiniteDimensional.complete ℝ R

local instance finiteDimensionalLeftInvariantDerivationAdjointUnitsExponential :
    FiniteDimensional ℝ (LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

/-- On algebra units, the abstract adjoint of `lieExp X` is the bounded-operator exponential of
Mathlib's Lie-algebra adjoint `ad X`. -/
theorem Ad_lieExp_units (X : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    let adX := LinearMap.toContinuousLinearMap
      (LieAlgebra.ad ℝ (LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) X)
    (Ad (I := 𝓘(ℝ, R)) (lieExp X)).toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap =
      exp adX := by
  dsimp only
  let e := (unitsLieAlgebraEquiv (R := R)).toContinuousLinearEquiv
  apply e.conjContinuousAlgEquiv.injective
  have hmap := NormedSpace.map_exp e.conjContinuousAlgEquiv
    e.conjContinuousAlgEquiv.continuous
      (LinearMap.toContinuousLinearMap
        (LieAlgebra.ad ℝ (LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) X))
  rw [unitsLieAlgebraEquiv_ad] at hmap
  calc
    e.conjContinuousAlgEquiv
        (Ad (I := 𝓘(ℝ, R)) (lieExp X)).toLinearEquiv.toContinuousLinearEquiv =
        exp (continuousCommutator (unitsLieAlgebraEquiv X)) := by
      apply ContinuousLinearMap.ext
      intro Y
      rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
      -- Conjugation is bundled through continuous-linear equivalences, whereas `Ad` acts on the
      -- underlying derivations; expose that evaluation before applying the units transport laws.
      change unitsLieAlgebraEquiv (Ad (I := 𝓘(ℝ, R)) (lieExp X)
        ((unitsLieAlgebraEquiv (R := R)).symm Y)) =
          exp (continuousCommutator (unitsLieAlgebraEquiv X)) Y
      rw [unitsLieAlgebraEquiv_Ad, lieExp_eq_expUnit,
        exp_continuousCommutator_apply, LinearEquiv.apply_symm_apply]
      rw [← TauCeti.expUnit_neg]
      simp only [TauCeti.expUnit_coe]
    _ = e.conjContinuousAlgEquiv
        (exp (LinearMap.toContinuousLinearMap
          (LieAlgebra.ad ℝ (LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) X))) := hmap.symm

end FiniteDimensional

end TauCeti.Lie
