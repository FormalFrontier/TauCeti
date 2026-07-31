/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Moments
public import TauCeti.Probability.Process.EmpiricalMeasure

/-!
# Empirical measures of conditionally i.i.d. processes

This file expresses the empirical-frequency estimates for a conditionally i.i.d. process in terms
of the empirical probability measure.  For every measurable set, evaluation of the empirical
measure converges in mean square to evaluation of the directing measure, with the exact
finite-sample error and its `1 / (n + 1)` bound.

These results are the setwise input to the empirical-measure form of de Finetti's theorem in Layer 6
of the `Exchangeability` roadmap.  They reuse the conditional moment identities already proved in
`ConditionallyIID.Moments`; the new content is the connection to the process-level
`empiricalMeasure` object.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} {B : Set α}

/-- The exact mean-square error of empirical-measure evaluation for a conditionally i.i.d.
process.  At sample size `n + 1`, the error is the Bernoulli variance of the directing measure's
mass on `B`, divided by `n + 1`. -/
theorem ConditionallyIIDWith.integral_empiricalMeasure_apply_sub_sq [IsProbabilityMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ)
    (hB : MeasurableSet B) (n : ℕ) :
    ∫ ω, ((((empiricalMeasure (fun i => X i ω) n : ProbabilityMeasure α) : Measure α) B).toReal
          - ((ν ω : Measure α) B).toReal) ^ 2 ∂μ =
      ((n + 1 : ℕ) : ℝ)⁻¹ *
        (∫ ω, ((ν ω : Measure α) B).toReal ∂μ -
          ∫ ω, ((ν ω : Measure α) B).toReal ^ 2 ∂μ) := by
  simpa only [empiricalMeasure_process_apply_toReal hB] using
    h.integral_empiricalFrequency_sub_sq hX hB (n := n + 1) (Nat.succ_ne_zero n)

/-- Empirical-measure evaluation has mean-square error at most `1 / (n + 1)`. -/
theorem ConditionallyIIDWith.integral_empiricalMeasure_apply_sub_sq_le
    [IsProbabilityMeasure μ] (h : ConditionallyIIDWith μ X ν)
    (hX : ∀ i, AEMeasurable (X i) μ) (hB : MeasurableSet B) (n : ℕ) :
    ∫ ω, ((((empiricalMeasure (fun i => X i ω) n : ProbabilityMeasure α) : Measure α) B).toReal
          - ((ν ω : Measure α) B).toReal) ^ 2 ∂μ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
  simpa only [empiricalMeasure_process_apply_toReal hB] using
    h.integral_empiricalFrequency_sub_sq_le hX hB (n := n + 1) (Nat.succ_ne_zero n)

/-- For every measurable set, evaluation of the empirical measure of a conditionally i.i.d.
process converges in mean square to evaluation of its directing measure. -/
theorem ConditionallyIIDWith.tendsto_integral_empiricalMeasure_apply_sub_sq
    [IsProbabilityMeasure μ] (h : ConditionallyIIDWith μ X ν)
    (hX : ∀ i, AEMeasurable (X i) μ) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ =>
      ∫ ω, ((((empiricalMeasure (fun i => X i ω) n : ProbabilityMeasure α) : Measure α) B).toReal
            - ((ν ω : Measure α) B).toReal) ^ 2 ∂μ) atTop (nhds 0) := by
  simpa only [empiricalMeasure_process_apply_toReal hB] using
    h.tendsto_integral_empiricalFrequency_sub_sq hX hB

end Probability

end TauCeti
