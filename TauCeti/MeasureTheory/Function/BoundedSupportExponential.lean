/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Exponential moments from bounded support

This file records a small bounded-support integrability principle used by the
`OrthogonalL2Bases` roadmap's moment-determinacy route.  If a measure is supported where the
argument norm is essentially bounded, multiplying an integrable function by any exponential
weight `exp (a * ‖x‖)` preserves integrability.  On `ℝ`, this gives the corresponding
`exp (a * |x|)` form.

The Chebyshev `T` measure is supported on `[-1, 1]`, so this is the reusable bookkeeping behind
the finite exponential moments needed before the Chebyshev Hilbert-basis construction.
-/

public section

namespace TauCeti

open MeasureTheory

variable {α 𝕜 β : Type*} [NormedAddCommGroup α] [MeasurableSpace α] [OpensMeasurableSpace α]
variable [RCLike 𝕜] [SecondCountableTopologyEither α 𝕜] [NormedAddCommGroup β]
variable [NormedSpace 𝕜 β] {μ : Measure α} {g : α → β}

/-- Multiplication by `exp (a * ‖x‖)` preserves integrability on a measure whose support is
essentially contained in a closed ball. -/
protected theorem Integrable.exp_norm_smul_of_ae_norm_le (hg : Integrable g μ) (a R : ℝ)
    (hR : ∀ᵐ x ∂μ, ‖x‖ ≤ R) :
    Integrable (fun x : α => (Real.exp (a * ‖x‖) : 𝕜) • g x) μ := by
  have h_exp : AEStronglyMeasurable (fun x : α => (Real.exp (a * ‖x‖) : 𝕜)) μ := by
    exact (RCLike.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_norm))).aestronglyMeasurable
  refine hg.bdd_smul (Real.exp (|a| * max R 0)) h_exp ?_
  filter_upwards [hR] with x hx
  have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
  have hx_bound : ‖x‖ ≤ max R 0 := hx.trans (le_max_left R 0)
  have hmul_left : a * ‖x‖ ≤ |a| * ‖x‖ :=
    mul_le_mul_of_nonneg_right (le_abs_self a) hx_nonneg
  have hmul_right : |a| * ‖x‖ ≤ |a| * max R 0 :=
    mul_le_mul_of_nonneg_left hx_bound (abs_nonneg a)
  simpa [RCLike.norm_ofReal] using
    Real.exp_le_exp.mpr (hmul_left.trans hmul_right)

/-- Real-line version of `Integrable.exp_norm_smul_of_ae_norm_le`, stated with `|x|`. -/
protected theorem Integrable.exp_abs_smul_of_ae_abs_le {μ : Measure ℝ} {g : ℝ → β}
    (hg : Integrable g μ) (a R : ℝ) (hR : ∀ᵐ x ∂μ, |x| ≤ R) :
    Integrable (fun x : ℝ => (Real.exp (a * |x|) : 𝕜) • g x) μ := by
  simpa [Real.norm_eq_abs] using
    (Integrable.exp_norm_smul_of_ae_norm_le (α := ℝ) hg a R
      (by simpa [Real.norm_eq_abs] using hR))

end TauCeti
