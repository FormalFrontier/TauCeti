/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Units.Basic

/-!
# Exponential compatibility of the adjoint action on algebra units

For the Lie group of units of a complete real normed algebra, the tangent adjoint of an exponential
is the exponential of the continuous commutator operator.

## Main result

* `tangentAd_expUnit`: the tangent adjoint of an algebra-unit exponential is the exponential of the
  continuous commutator.

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

end TauCeti.Lie
