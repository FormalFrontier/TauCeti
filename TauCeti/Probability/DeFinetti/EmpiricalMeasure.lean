/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.EmpiricalMeasure
public import TauCeti.Probability.DeFinetti.Theorem
-- Non-public: conditional weak convergence is used only to prove the endpoint below; this module
-- does not re-export the `ConditionallyIIDWith.*` convergence API.
import TauCeti.Probability.Exchangeability.ConditionallyIID.WeakConvergence

/-!
# De Finetti's theorem in empirical form

The de Finetti endpoints of the conditional strong law: for an exchangeable process on a nonempty
standard Borel space, the directing measure's mass on each fixed measurable set is the almost-sure
limit of the process's empirical frequencies, and — once a compatible Polish topology on the state
space is fixed — the directing measure is itself the almost-sure weak limit of the empirical
measures.

These are the meeting point of two independent inputs, and it is why they live in their own module.
The analytic content is `ConditionallyIIDWith.tendsto_empiricalMeasure_apply_ae` and
`ConditionallyIIDWith.tendsto_empiricalMeasure_ae`, stated for a *conditionally i.i.d.* process and
needing no standard-Borel structure; the existence of the directing measure for an *exchangeable*
process is `conditionallyIID_of_exchangeable`, the de Finetti summit. Keeping the two apart lets a
caller import the conditional strong law without also importing the summit, which is a
substantially larger closure.

The two endpoints differ in what they assume of the state space, not merely in strength.
`[StandardBorelSpace α]` selects no topology, so it supports the fixed-set statement but cannot even
express weak convergence; the weak form therefore asks for a Polish topology and the Borel
σ-algebra it generates, which in particular makes `α` standard Borel.

## Main results

* `deFinetti_tendsto_empiricalMeasure_apply` — for an exchangeable process on a standard Borel state
  space, a directing measure whose mass on each fixed measurable set is recovered as the almost-sure
  limit of the empirical frequencies;
* `deFinetti_empiricalMeasure` — for an exchangeable process on a Polish state space, a directing
  measure that is the almost-sure weak limit of the empirical measures.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 6's empirical form of the
  directing-measure theorem, in both its topology-free fixed-set version and its
  weak-convergence version.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles* (Springer, 2005), §1.1.

No material is adapted from `cameronfreer/exchangeability`, which does not treat empirical measures.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α}

/-- **De Finetti's theorem in empirical-frequency form.** An exchangeable process valued in a
nonempty standard Borel space has a directing measure whose mass on each fixed measurable set is
recovered, almost surely, as the limit of the empirical frequencies of the process.

The directing measure is thus not merely asserted to exist: each of its values is the pathwise
limit of an explicit statistic of the process. The null set depends on the set tested, as it must.
The weak-topology form of the same statement, testing against bounded continuous functions
simultaneously, is `deFinetti_empiricalMeasure` below, which additionally assumes a compatible
Polish topology on `α` and its Borel σ-algebra. -/
theorem deFinetti_tendsto_empiricalMeasure_apply [StandardBorelSpace α] [Nonempty α]
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ n, AEMeasurable (X n) μ) :
    ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν ∧
      ∀ B : Set α, MeasurableSet B → ∀ᵐ ω ∂μ, Tendsto
        (fun n : ℕ => ((empiricalMeasure (fun i => X i ω) n : Measure α) B).toReal) atTop
        (𝓝 (((ν ω : Measure α) B).toReal)) := by
  obtain ⟨ν, hν⟩ := (conditionallyIID_of_exchangeable hX hX_meas).exists_directing
  exact ⟨ν, hν, fun B hB => hν.tendsto_empiricalMeasure_apply_ae hX_meas hB⟩

/-- **De Finetti's theorem in empirical-measure form.** An exchangeable process valued in a
nonempty Polish space, with its Borel σ-algebra, has a directing measure that is almost surely the
weak limit of the empirical measures of the process — the limit is in the topology of convergence
in distribution on `ProbabilityMeasure α`, so it tests against all bounded continuous functions
simultaneously.

The directing measure is thus recovered from the process by an explicit pathwise limit, and not
merely one measurable set at a time as in `deFinetti_tendsto_empiricalMeasure_apply`. A Polish
topology is assumed rather than produced: `[StandardBorelSpace α]` alone fixes no topology on `α`,
and different compatible topologies give different weak topologies on `ProbabilityMeasure α`. -/
theorem deFinetti_empiricalMeasure [TopologicalSpace α] [PolishSpace α] [BorelSpace α] [Nonempty α]
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ n, AEMeasurable (X n) μ) :
    ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => empiricalMeasure (fun i => X i ω) n) atTop (𝓝 (ν ω)) := by
  obtain ⟨ν, hν⟩ := (conditionallyIID_of_exchangeable hX hX_meas).exists_directing
  exact ⟨ν, hν, hν.tendsto_empiricalMeasure_ae hX_meas⟩

end Probability

end TauCeti
