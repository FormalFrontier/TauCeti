/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.BanachDexp.Basic
public import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Integral

/-!
# The integral action formula for the Banach dexp factor

This file rewrites the filled commutator quotient as an integral of conjugations. It is the
Banach-algebra shadow of the left-trivialized differential-of-exponential factor.

## Main results

* `TauCeti.Lie.banachDexpFactor_eq_integral_exp`: the dexp factor is an integral of operator
  exponentials.
* `TauCeti.Lie.banachDexpFactor_apply_eq_integral_conj`: on an algebra element, the integrand is
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

/-- Real continuous endomorphisms regarded as a rational normed algebra in this module. -/
noncomputable local instance normedAlgebraRatContinuousLinearMapRealId :
    NormedAlgebra ℚ (R →L[ℝ] R) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- The Banach dexp factor is the integral of the corresponding operator exponential. -/
theorem banachDexpFactor_eq_integral_exp (x : R) :
    banachDexpFactor x =
      ∫ t in (0 : ℝ)..1, exp (t • (-continuousCommutator x)) := by
  rw [banachDexpFactor_eq_oneSubExpNegDivSelf, oneSubExpNegDivSelf_eq_integral_exp]

/-- Applied to an algebra element, the Banach dexp factor is the integral of conjugation by
`exp (-t x)`. -/
theorem banachDexpFactor_apply_eq_integral_conj (x y : R) :
    banachDexpFactor x y =
      ∫ t in (0 : ℝ)..1, exp ((-t) • x) * y * exp (t • x) := by
  rw [banachDexpFactor_eq_integral_exp]
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ exp (t • (-continuousCommutator x))) volume 0 1 :=
    Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply (μ := volume) hint y]
  apply intervalIntegral.integral_congr
  intro t _ht
  -- Applying the operator-valued exponential to `y` unfolds definitionally after the
  -- pointwise interval-integral lemma above.
  change exp (t • (-continuousCommutator x)) y =
    exp ((-t) • x) * y * exp (t • x)
  have hscale :
      t • (-continuousCommutator x) = continuousCommutator ((-t) • x) := by
    ext z
    simp [continuousCommutator_apply, smul_sub]
  rw [hscale, exp_continuousCommutator_apply]
  simp

end TauCeti.Lie
