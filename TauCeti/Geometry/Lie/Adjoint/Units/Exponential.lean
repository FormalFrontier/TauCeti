/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.OperatorExponential
public import TauCeti.Geometry.Lie.Adjoint.Units.Basic

/-!
# Exponential compatibility of the adjoint action on algebra units

For the Lie group of units of a complete real normed algebra, the tangent adjoint of an exponential
is the exponential of the continuous commutator operator. In finite dimensions, this transports to
the abstract identity `Ad (lieExp X) = exp (ad X)` on left-invariant derivations.

## Main result

* `tangentAd_expUnit`: the tangent adjoint of an algebra-unit exponential is the exponential of the
  continuous commutator.
* `unitsLieAlgebraEquiv_Ad_lieExp`: the corresponding finite-dimensional identity transported to
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

/-- On algebra units, `Ad (lieExp X)` is the exponential of the continuous commutator by the
ambient algebra element corresponding to `X`. -/
@[simp high]
theorem unitsLieAlgebraEquiv_Ad_lieExp
    (X Y : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    unitsLieAlgebraEquiv (Ad (I := 𝓘(ℝ, R)) (lieExp X) Y) =
      exp (continuousCommutator (unitsLieAlgebraEquiv X))
        (unitsLieAlgebraEquiv Y) := by
  rw [unitsLieAlgebraEquiv_Ad, lieExp_eq_expUnit,
    exp_continuousCommutator_apply]
  rw [← TauCeti.expUnit_neg]
  simp only [TauCeti.expUnit_coe]

end FiniteDimensional

end TauCeti.Lie
