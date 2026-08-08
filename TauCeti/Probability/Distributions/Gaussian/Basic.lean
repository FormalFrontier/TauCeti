/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Closed forms for the real Gaussian density

Mathlib's `ProbabilityTheory.gaussianPDFReal μ v` is stated for a general mean `μ` and variance `v`.
This file records the specialization at the standard parameters `μ = 0`, `v = 1`, where the shift
and the variance both disappear and the density collapses to `(√(2π))⁻¹ · e^{-x²/2}`.

That closed form is what any calculation against the standard Gaussian weight rewrites by, and it
is a statement about the Gaussian distribution alone: it mentions no orthogonal family, so it
belongs here rather than in any of the families that consume it (the Hermite orthogonality
relation and the Gaussian Hermite basis both do).

## Main statements

* `TauCeti.gaussianPDFReal_zero_one` — `gaussianPDFReal 0 1 x = (√(2π))⁻¹ · e^{-x²/2}`.
-/

public section

namespace TauCeti

open ProbabilityTheory Real

/-- The probability-density form of the standard Gaussian weight:
`gaussianPDFReal 0 1 x = (√(2π))⁻¹ · e^{-x²/2}`. -/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [show -x ^ 2 / 2 = -(x ^ 2 / 2) from by ring]

end TauCeti
