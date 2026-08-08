/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.Topology.Semicontinuity.Approximation

/-!
# Lower semicontinuity of a lower semicontinuous integrand in the measure

Fix a lower semicontinuous `f : Ω → ℝ≥0∞` on a pseudometric space. This file proves that the
pairing `μ ↦ ∫⁻ x, f x ∂μ` is lower semicontinuous for the weak topology on `FiniteMeasure Ω` and
on `ProbabilityMeasure Ω`, together with the two consequences the direct method of the calculus of
variations runs on: the `liminf` inequality along a weakly convergent family, and attainment of the
infimum on a nonempty compact set of measures.

For a bounded continuous integrand the pairing is *continuous* — that is what the weak topology is
defined by. The content here is that dropping boundedness and continuity down to lower
semicontinuity costs exactly one half of that continuity, and no integrability hypothesis at all:
the value `∞` is allowed on both sides.

## Main results

* `TauCeti.lowerSemicontinuous_lintegral_finiteMeasure` and
  `TauCeti.lowerSemicontinuous_lintegral_probabilityMeasure`: the pairing is lower semicontinuous.
* `TauCeti.le_liminf_lintegral_of_tendsto`: the `liminf` form along a weakly convergent family.
* `TauCeti.exists_isMinOn_lintegral`: a nonempty compact set of probability measures contains one
  minimising the integral, with no finiteness assumption on the minimum value.
* `TauCeti.isClosed_setOf_lintegral_le`: the sublevel sets of the pairing are closed.

## Implementation notes

The proof is the standard monotone-approximation argument: `TauCeti.lscApprox` writes `f` as the
pointwise supremum of an increasing sequence of bounded continuous `ℝ≥0`-valued functions, the
monotone convergence theorem turns that into a supremum of integrals, each summand is continuous in
the measure because it is a weak-topology test function, and a supremum of continuous functions is
lower semicontinuous.

Only `OpensMeasurableSpace Ω` is used on the measurable side: it is what makes a lower
semicontinuous function measurable, and Mathlib's weak topology is already available at that
generality.
-/

public section

open Filter MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
  {f : Ω → ℝ≥0∞}

/-- Monotone convergence applied to the approximating sequence `TauCeti.lscApprox`: the
integral of a lower semicontinuous `f` is the supremum of the integrals of bounded continuous
test functions below it. -/
theorem lintegral_eq_iSup_lintegral_lscApprox (hf : LowerSemicontinuous f) (μ : Measure Ω) :
    ∫⁻ x, f x ∂μ = ⨆ n : ℕ, ∫⁻ x, (lscApprox f n x : ℝ≥0∞) ∂μ := by
  rw [← lintegral_iSup (fun n ↦ (lscApprox f n).continuous.measurable.coe_nnreal_ennreal)
    (monotone_coe_lscApprox f)]
  exact lintegral_congr fun x ↦ (iSup_coe_lscApprox hf x).symm

/-- Integration of a lower semicontinuous `f : Ω → ℝ≥0∞` is lower semicontinuous in the finite
measure, for the topology of weak convergence. -/
theorem lowerSemicontinuous_lintegral_finiteMeasure (hf : LowerSemicontinuous f) :
    LowerSemicontinuous fun μ : FiniteMeasure Ω ↦ ∫⁻ x, f x ∂(μ : Measure Ω) := by
  have h : (fun μ : FiniteMeasure Ω ↦ ∫⁻ x, f x ∂(μ : Measure Ω)) =
      fun μ : FiniteMeasure Ω ↦ ⨆ n : ℕ, ∫⁻ x, (lscApprox f n x : ℝ≥0∞) ∂(μ : Measure Ω) :=
    funext fun μ ↦ lintegral_eq_iSup_lintegral_lscApprox hf _
  rw [h]
  exact lowerSemicontinuous_iSup fun n ↦
    (FiniteMeasure.continuous_lintegral_boundedContinuousFunction
      (lscApprox f n)).lowerSemicontinuous

/-- Integration of a lower semicontinuous `f : Ω → ℝ≥0∞` is lower semicontinuous in the
probability measure, for the topology of weak convergence. -/
theorem lowerSemicontinuous_lintegral_probabilityMeasure (hf : LowerSemicontinuous f) :
    LowerSemicontinuous fun μ : ProbabilityMeasure Ω ↦ ∫⁻ x, f x ∂(μ : Measure Ω) := by
  intro μ a ha
  have h := lowerSemicontinuous_lintegral_finiteMeasure hf μ.toFiniteMeasure a (by simpa using ha)
  filter_upwards [ProbabilityMeasure.toFiniteMeasure_continuous.continuousAt.eventually h]
    with ν hν using by simpa using hν

/-- The `liminf` form of lower semicontinuity: along a weakly convergent family of probability
measures, the integral of a lower semicontinuous integrand can only drop in the limit. -/
theorem le_liminf_lintegral_of_tendsto {γ : Type*} {L : Filter γ} {μs : γ → ProbabilityMeasure Ω}
    {μ : ProbabilityMeasure Ω} (hf : LowerSemicontinuous f) (h : Tendsto μs L (𝓝 μ)) :
    ∫⁻ x, f x ∂(μ : Measure Ω) ≤ liminf (fun i ↦ ∫⁻ x, f x ∂(μs i : Measure Ω)) L := by
  refine ((lowerSemicontinuous_lintegral_probabilityMeasure hf).le_liminf μ).trans ?_
  simpa [Function.comp_def] using h.liminf_le_liminf_comp
    (u := fun ν : ProbabilityMeasure Ω ↦ ∫⁻ x, f x ∂(ν : Measure Ω))

/-- The same `liminf` inequality for a weakly convergent family of finite measures. -/
theorem le_liminf_lintegral_of_tendsto_finiteMeasure {γ : Type*} {L : Filter γ}
    {μs : γ → FiniteMeasure Ω} {μ : FiniteMeasure Ω} (hf : LowerSemicontinuous f)
    (h : Tendsto μs L (𝓝 μ)) :
    ∫⁻ x, f x ∂(μ : Measure Ω) ≤ liminf (fun i ↦ ∫⁻ x, f x ∂(μs i : Measure Ω)) L := by
  refine ((lowerSemicontinuous_lintegral_finiteMeasure hf).le_liminf μ).trans ?_
  simpa [Function.comp_def] using h.liminf_le_liminf_comp
    (u := fun ν : FiniteMeasure Ω ↦ ∫⁻ x, f x ∂(ν : Measure Ω))

/-- Sublevel sets of the pairing against a lower semicontinuous integrand are weakly closed. -/
theorem isClosed_setOf_lintegral_le (hf : LowerSemicontinuous f) (a : ℝ≥0∞) :
    IsClosed {μ : ProbabilityMeasure Ω | ∫⁻ x, f x ∂(μ : Measure Ω) ≤ a} :=
  (lowerSemicontinuous_lintegral_probabilityMeasure hf).isClosed_preimage a

/-- The direct method of the calculus of variations for a lower semicontinuous integrand: on a
nonempty compact set of probability measures, the integral attains its infimum. The minimum value
is allowed to be `∞`, which happens exactly when every measure in the set gives `f` infinite
integral. -/
theorem exists_isMinOn_lintegral {K : Set (ProbabilityMeasure Ω)} (hK : K.Nonempty)
    (hKc : IsCompact K) (hf : LowerSemicontinuous f) :
    ∃ μ ∈ K, IsMinOn (fun ν : ProbabilityMeasure Ω ↦ ∫⁻ x, f x ∂(ν : Measure Ω)) K μ :=
  ((lowerSemicontinuous_lintegral_probabilityMeasure hf).lowerSemicontinuousOn K).exists_isMinOn
    hK hKc

/-- The infimum of the integral over a nonempty compact set of probability measures is a minimum:
it is the value at some member of the set. -/
theorem exists_lintegral_eq_iInf {K : Set (ProbabilityMeasure Ω)} (hK : K.Nonempty)
    (hKc : IsCompact K) (hf : LowerSemicontinuous f) :
    ∃ μ ∈ K, ∫⁻ x, f x ∂(μ : Measure Ω) =
      ⨅ ν : K, ∫⁻ x, f x ∂((ν : ProbabilityMeasure Ω) : Measure Ω) := by
  obtain ⟨μ, hμK, hμ⟩ := exists_isMinOn_lintegral hK hKc hf
  refine ⟨μ, hμK, le_antisymm ?_ (iInf_le_of_le ⟨μ, hμK⟩ le_rfl)⟩
  exact le_iInf fun ν ↦ hμ ν.2

end TauCeti
