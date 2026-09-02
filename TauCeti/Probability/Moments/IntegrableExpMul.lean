/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Integrability of exponential moments

This file records measure-agnostic exponential-integrability criteria for random variables.

## Main results

* `TauCeti.integrable_exp_mul_of_ae_le_of_nonpos`: `exp (t * X ·)` is integrable for `t ≤ 0`
  whenever `X` is almost everywhere bounded below under a finite measure.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

/-- Under a finite measure, the exponential of a nonpositive multiple of an almost everywhere
bounded below random variable is integrable.

This is Mathlib's `ProbabilityTheory.integrable_exp_mul_of_le` reflected through `X ↦ -X`. -/
theorem integrable_exp_mul_of_ae_le_of_nonpos {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (hX : AEMeasurable X μ)
    {b : ℝ} (hb : ∀ᵐ ω ∂μ, b ≤ X ω) {t : ℝ} (ht : t ≤ 0) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  simpa only [Pi.neg_apply, neg_mul_neg] using
    ProbabilityTheory.integrable_exp_mul_of_le (-t) (-b) (neg_nonneg.mpr ht) hX.neg
      (by filter_upwards [hb] with ω hω using neg_le_neg hω)

end TauCeti
