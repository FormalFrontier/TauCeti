/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.StrongLaw
-- Non-public: the π-system criterion for weak convergence is used only inside proofs.
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# The empirical measures of a conditionally i.i.d. process converge weakly

The conditional strong law gives, for each *fixed* measurable set, almost-sure convergence of the
empirical frequencies of a conditionally i.i.d. process to the mass the directing measure gives
that set. This file makes the limit a statement about the empirical measures themselves: almost
surely, `empiricalMeasure (X · ω) n → ν ω` in the topology of convergence in distribution on
`ProbabilityMeasure α`.

Weak convergence tests against all bounded continuous functions at once, so the null set has to be
chosen before the test function is seen, and the fixed-set statement cannot simply be quantified
afterwards — outside a countable family of sets that interchange is false (see
`ConditionallyIID/StrongLaw.lean`). What makes the upgrade go through is that a second-countable
topology has a countable test class: the finite intersections of a countable basis, on which
`ConditionallyIIDWith.tendsto_empiricalMeasure_apply_ae_forall` provides a single null set, and
from which `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` recovers weak convergence —
they form a π-system containing arbitrarily small neighbourhoods of every point.

The hypotheses on the state space are topological, not standard Borel: a second-countable
topology whose open sets are measurable is all the argument uses. In particular a Polish space
with its Borel σ-algebra qualifies, which is the form in which the roadmap states the result.

## Main results

* `ConditionallyIIDWith.tendsto_empiricalMeasure_ae` — almost surely, the empirical measures
  converge weakly to the directing measure.

The de Finetti endpoint, where the directing measure of an *exchangeable* process has to be
produced first, is `deFinetti_empiricalMeasure` in `DeFinetti/EmpiricalMeasure.lean`.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 6, weak empirical-measure convergence.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles* (Springer, 2005), §1.1.

No material is adapted from `cameronfreer/exchangeability`, which does not treat empirical measures.
-/

public section

noncomputable section

open Filter MeasureTheory TopologicalSpace

open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [TopologicalSpace α]
  [SecondCountableTopology α] [OpensMeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}

/-- **The empirical measures of a conditionally i.i.d. process converge weakly to its directing
measure, almost surely.** The convergence is in the topology of convergence in distribution on
`ProbabilityMeasure α`, and the null set is one and the same for every test function.

This is the measure-valued form of `ConditionallyIIDWith.tendsto_empiricalMeasure_apply_ae`, which
gives the same limit one measurable set at a time. It is not a formal consequence of that
statement: the null set there may be chosen after the fixed set, and no null set works for every
measurable set simultaneously. -/
theorem ConditionallyIIDWith.tendsto_empiricalMeasure_ae [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ n, AEMeasurable (X n) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => empiricalMeasure (fun i => X i ω) n) atTop (𝓝 (ν ω)) := by
  obtain ⟨B, hB⟩ := exists_seq_basis α
  set T : Finset ℕ → Set α := fun s => ⋂ i ∈ s, B i with hT
  have hBopen : ∀ i, IsOpen (B i) := fun i => hB.isOpen (Set.mem_range_self i)
  have hTmeas : ∀ s, MeasurableSet (T s) := fun s =>
    s.measurableSet_biInter fun i _ => (hBopen i).measurableSet
  -- The finite intersections of the basis sets are a countable π-system of measurable sets
  -- containing arbitrarily small neighbourhoods of every point.
  have hpi : IsPiSystem (Set.range T) := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ -
    exact ⟨s ∪ t, by
      simp only [hT, ← Finset.set_biInter_coe, Finset.coe_union, Set.biInter_union]⟩
  filter_upwards [h.tendsto_empiricalMeasure_apply_ae_forall (B := T) hX hTmeas] with ω hω
  refine hpi.tendsto_probabilityMeasure_of_tendsto_of_mem ?_ (fun u hu x hxu => ?_) ?_
  · rintro _ ⟨s, rfl⟩
    exact hTmeas s
  · obtain ⟨-, ⟨i, rfl⟩, hxi, hiu⟩ := hB.exists_subset_of_mem_open hxu hu
    exact ⟨T {i}, Set.mem_range_self _, by simpa [hT] using (hBopen i).mem_nhds hxi,
      by simpa [hT] using hiu⟩
  · rintro _ ⟨s, rfl⟩
    exact NNReal.tendsto_coe.1 <| by
      simpa only [← ProbabilityMeasure.measureReal_eq_coe_coeFn, measureReal_def] using hω s

end Probability

end TauCeti
