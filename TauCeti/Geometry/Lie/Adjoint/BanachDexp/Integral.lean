/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.BanachDexp.Basic
public import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Integral
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# The integral action formula for the Banach dexp factor

This file rewrites the filled commutator quotient as an integral of conjugations. It is the
Banach-algebra shadow of the left-trivialized differential-of-exponential factor.

## Main results

* `TauCeti.Lie.banachDexpFactor_eq_integral_exp`: the dexp factor is the integral of the operator
  exponential along the line segment from `0` to `-ad x`.
* `TauCeti.Lie.banachDexpFactor_apply_eq_integral`: on an algebra element, the integrand is
  conjugation by `exp (-t x)`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

noncomputable section

namespace TauCeti.Lie

open NormedSpace MeasureTheory

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- The Banach dexp factor is the integral of the operator exponential along the line segment from
`0` to `-ad x`. -/
theorem banachDexpFactor_eq_integral_exp (x : R) :
    banachDexpFactor x =
      ∫ t in (0 : ℝ)..1, exp (-(t • continuousCommutator x)) := by
  rw [banachDexpFactor_eq_oneSubExpNegDivSelf]
  simpa only [smul_neg] using oneSubExpNegDivSelf_eq_integral_exp
    (A := R →L[ℝ] R) (continuousCommutator x)

/-- Applied to an algebra element, the Banach dexp factor is the integral of conjugation by
`exp (-t x)`. -/
theorem banachDexpFactor_apply_eq_integral (x y : R) :
    banachDexpFactor x y =
      ∫ t in (0 : ℝ)..1, exp (-(t • x)) * y * exp (t • x) := by
  rw [banachDexpFactor_eq_integral_exp]
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ exp (-(t • continuousCommutator x))) volume 0 1 :=
    Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply (μ := volume) hint y]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  have hscale :
      -(t • continuousCommutator x) = continuousCommutator ((-t) • x) := by
    calc
      -(t • continuousCommutator x) = (-t) • continuousCommutator x := (neg_smul _ _).symm
      _ = continuousCommutator ((-t) • x) := (map_smul _ _ _).symm
  rw [hscale, exp_continuousCommutator_apply]
  simp

end TauCeti.Lie
