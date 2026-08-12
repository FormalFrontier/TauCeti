/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.OperatorExponential
public import TauCeti.Geometry.Lie.Adjoint.Units

/-!
# Exponential compatibility of the adjoint action on algebra units

For the Lie group of units of a finite-dimensional real normed algebra, the abstract identity
`Ad (lieExp X) = exp (ad X)` becomes the exponential of the continuous commutator operator. This
combines the abstract conjugation formula with the Banach-algebra operator exponential.

## Main result

* `unitsLieAlgebraEquiv_Ad_lieExp`: the transported abstract adjoint exponential agrees pointwise
  with the exponential of the continuous commutator.

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

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

local instance finiteDimensionalCompleteSpaceAdjointUnitsExponential : CompleteSpace R :=
  FiniteDimensional.complete ℝ R

/-- On algebra units, `Ad (lieExp X)` is the exponential of the continuous commutator by the
ambient algebra element corresponding to `X`. -/
theorem unitsLieAlgebraEquiv_Ad_lieExp
    (X Y : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    unitsLieAlgebraEquiv (Ad (I := 𝓘(ℝ, R)) (lieExp X) Y) =
      exp (continuousCommutator (unitsLieAlgebraEquiv X))
        (unitsLieAlgebraEquiv Y) := by
  rw [unitsLieAlgebraEquiv_Ad, lieExp_eq_expUnit,
    exp_continuousCommutator_apply]
  rw [← TauCeti.expUnit_neg]
  simp only [TauCeti.expUnit_coe]

end TauCeti.Lie
