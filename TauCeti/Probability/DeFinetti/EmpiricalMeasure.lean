/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.EmpiricalMeasure
public import TauCeti.Probability.DeFinetti.Theorem
-- Non-public: the conditional strong law is used only to prove the endpoint below; this module
-- does not re-export the `ConditionallyIIDWith.*` strong-law API.
import TauCeti.Probability.Exchangeability.ConditionallyIID.StrongLaw

/-!
# De Finetti's theorem in empirical-frequency form

The de Finetti endpoint of the conditional strong law: for an exchangeable process on a nonempty
standard Borel space, the directing measure's mass on each fixed measurable set is the almost-sure
limit of the process's empirical frequencies.

This is the meeting point of two independent inputs, and it is why it lives in its own module. The
analytic content is `ConditionallyIIDWith.tendsto_empiricalMeasure_apply_ae`, which is stated for a
*conditionally i.i.d.* process and needs no standard-Borel structure; the existence of the directing
measure for an *exchangeable* process is `conditionallyIID_of_exchangeable`, the de Finetti summit.
Keeping the two apart lets a caller import the conditional strong law without also importing the
summit, which is a substantially larger closure.

## Main results

* `deFinetti_tendsto_empiricalMeasure_apply` — for an exchangeable process on a standard Borel state
  space, a directing measure whose mass on each fixed measurable set is recovered as the almost-sure
  limit of the empirical frequencies.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 6's empirical form of the
  directing-measure theorem. This module supplies the topology-free fixed-set endpoint; weak
  empirical-measure convergence is a separate downstream theorem requiring a chosen compatible
  Polish topology, which `[StandardBorelSpace α]` does not select.
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
The weak-topology form of the same statement, testing against bounded continuous functions, needs a
compatible Polish topology on `α` and is not proved here. -/
theorem deFinetti_tendsto_empiricalMeasure_apply [StandardBorelSpace α] [Nonempty α]
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν ∧
      ∀ B : Set α, MeasurableSet B → ∀ᵐ ω ∂μ, Tendsto
        (fun n : ℕ => ((empiricalMeasure (fun i => X i ω) n : Measure α) B).toReal) atTop
        (𝓝 (((ν ω : Measure α) B).toReal)) := by
  obtain ⟨ν, hν⟩ := (conditionallyIID_of_exchangeable hX fun n => (hX_meas n).aemeasurable)
    |>.exists_directing
  exact ⟨ν, hν, fun B hB =>
    hν.tendsto_empiricalMeasure_apply_ae (fun i => (hX_meas i).aemeasurable) hB⟩

end Probability

end TauCeti
