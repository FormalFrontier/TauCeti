/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import TauCeti.MeasureTheory.OptimalTransport.Coupling
-- Proof-only: Prokhorov's theorem, which upgrades tightness to relative compactness, and the
-- continuity of the pushforward of probability measures along a continuous map.
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# The transport plans of two probability measures form a compact set

The couplings of two fixed probability measures form a subset of the probability measures on the
product, and the weak topology restricts to it. This file proves that this set is weakly **closed**
and, on a Polish factor pair, weakly **compact**. Compactness is what makes the primal transport
problem solvable: a lower semicontinuous cost attains its infimum on a nonempty compact set.

The two halves are proved at their own generality and for their own reasons.

*Closedness* is a statement about the marginal maps. Pushing forward along the two coordinate
projections is continuous for the weak topology, and being a coupling of `μ` and `ν` says exactly
that the two pushforwards are `μ` and `ν`; so the coupling set is an intersection of two preimages
of points. That is closed as soon as points are closed in the two spaces of marginals, which is
the `T1Space` hypothesis carried here and is automatic in the Borel regime, where those spaces are
Hausdorff.

*Compactness* is Prokhorov's theorem. Tightness of the coupling set follows from tightness of the
two marginals alone: a compact rectangle `K₁ ×ˢ K₂` misses at most the mass its two sides miss,
uniformly over all couplings, because every coupling has the same two marginals. Tightness is
therefore stated for arbitrary measures with tight marginals, and the topological hypotheses enter
only when Prokhorov's theorem is applied.

## Main statements

* `TauCeti.isClosed_setOfPred_isCoupling` — the couplings of `μ` and `ν` are a weakly closed set of
  probability measures on the product;
* `TauCeti.isTightMeasureSet_setOfPred_isCoupling` — the couplings of two tight measures form a
  tight family, with no topological hypothesis beyond the two topologies themselves;
* `TauCeti.isCompact_setOfPred_isCoupling` — the couplings of `μ` and `ν` are a weakly compact set
  once both marginals are tight, and `TauCeti.isCompact_setOfPred_isCoupling_of_completeSpace` its
  Polish specialisation, where tightness is automatic;
* `TauCeti.Coupling.instCompactSpace` — the bundled coupling type is a compact space.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 4 — the tightness lemma for
  transference plans that precedes the existence theorem for an optimal coupling.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Springer 2015, Chapter 1 — the
  same compactness argument, run through Prokhorov's theorem.

This is Layer 1, items 2 and 3 of the optimal-transport roadmap.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section Marginal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : ProbabilityMeasure X}
  {ν : ProbabilityMeasure Y}

/-- Being a coupling, read on bundled probability measures: the two marginal pushforwards are the
prescribed marginals. This is the form in which the coupling condition is a pair of preimages of
points under continuous maps. -/
theorem isCoupling_toMeasure_iff {π : ProbabilityMeasure (X × Y)} :
    IsCoupling π.toMeasure μ.toMeasure ν.toMeasure ↔
      π.map measurable_fst.aemeasurable = μ ∧ π.map measurable_snd.aemeasurable = ν := by
  rw [← ProbabilityMeasure.toMeasure_injective.eq_iff (a := π.map measurable_fst.aemeasurable),
    ← ProbabilityMeasure.toMeasure_injective.eq_iff (a := π.map measurable_snd.aemeasurable),
    ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
  exact ⟨fun h ↦ ⟨h.fst_eq, h.snd_eq⟩, fun h ↦ ⟨h.1, h.2⟩⟩

end Marginal

section Closed

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopologyEither X Y]

/-- **The couplings of two probability measures are weakly closed.** The coupling set is the
intersection of the preimages of `{μ}` and `{ν}` under the two marginal maps, both of which are
continuous for the topology of convergence in distribution. The `T1Space` hypotheses are what make
the two singletons closed; in the Borel regime they hold, because the spaces of probability
measures are then Hausdorff. -/
theorem isClosed_setOfPred_isCoupling [T1Space (ProbabilityMeasure X)]
    [T1Space (ProbabilityMeasure Y)] (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    IsClosed {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} := by
  have hfst : Continuous fun π : ProbabilityMeasure (X × Y) ↦ π.map measurable_fst.aemeasurable :=
    ProbabilityMeasure.continuous_map (f := (Prod.fst : X × Y → X)) continuous_fst
  have hsnd : Continuous fun π : ProbabilityMeasure (X × Y) ↦ π.map measurable_snd.aemeasurable :=
    ProbabilityMeasure.continuous_map (f := (Prod.snd : X × Y → Y)) continuous_snd
  have hset : {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} =
      (fun π : ProbabilityMeasure (X × Y) ↦ π.map measurable_fst.aemeasurable) ⁻¹' {μ} ∩
        (fun π : ProbabilityMeasure (X × Y) ↦ π.map measurable_snd.aemeasurable) ⁻¹' {ν} := by
    ext π
    simpa only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff] using
      isCoupling_toMeasure_iff
  rw [hset]
  exact (isClosed_singleton.preimage hfst).inter (isClosed_singleton.preimage hsnd)

end Closed

section Tight

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y]
  [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

/-- **The couplings of two tight measures form a tight family.** Every coupling of `μ` and `ν`
gives the complement of a compact rectangle at most the mass that `μ` and `ν` give the complements
of its two sides, and those bounds are uniform in the coupling because the marginals are fixed. No
hypothesis beyond the two topologies is needed: the transport plans are exhausted by their two
marginals. -/
theorem isTightMeasureSet_setOfPred_isCoupling (hμ : IsTightMeasureSet {μ})
    (hν : IsTightMeasureSet {ν}) :
    IsTightMeasureSet {π : Measure (X × Y) | IsCoupling π μ ν} := by
  refine IsTightMeasureSet.prodMk (hμ.subset ?_) (hν.subset ?_)
  · rintro - ⟨π, hπ, rfl⟩
    exact hπ.fst_eq
  · rintro - ⟨π, hπ, rfl⟩
    exact hπ.snd_eq

end Tight

section Compact

/-! Prokhorov's theorem asks the underlying space to be Hausdorff and Borel, and the direct method
downstream asks it to be pseudometrizable, so the two factors are taken to be second countable
Borel metric spaces: their product is then again one, which is what the theorems below need. -/

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

/-- **The couplings of two tight probability measures are weakly compact.** The set is tight by
`TauCeti.isTightMeasureSet_setOfPred_isCoupling`, hence relatively compact by Prokhorov's theorem,
and it is closed by `TauCeti.isClosed_setOfPred_isCoupling`; so it equals its own closure and is
compact. -/
theorem isCompact_setOfPred_isCoupling {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (hμ : IsTightMeasureSet {μ.toMeasure}) (hν : IsTightMeasureSet {ν.toMeasure}) :
    IsCompact
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} := by
  have hclosed := isClosed_setOfPred_isCoupling μ ν
  have htight : IsTightMeasureSet {(π : ProbabilityMeasure (X × Y)).toMeasure |
      π ∈ {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure}} := by
    refine (isTightMeasureSet_setOfPred_isCoupling hμ hν).subset ?_
    rintro - ⟨π, hπ, rfl⟩
    exact hπ
  simpa only [hclosed.closure_eq] using isCompact_closure_of_isTightMeasureSet htight

/-- **The couplings of two probability measures on Polish spaces are weakly compact.** On a
complete, second countable metric space every finite Borel measure is tight, so the tightness
hypotheses of `TauCeti.isCompact_setOfPred_isCoupling` are automatic. This is the compactness that
the direct method of the calculus of variations consumes. -/
theorem isCompact_setOfPred_isCoupling_of_completeSpace [CompleteSpace X] [CompleteSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    IsCompact
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} :=
  isCompact_setOfPred_isCoupling isTightMeasureSet_singleton isTightMeasureSet_singleton

/-- The bundled type of couplings of two probability measures on Polish spaces is a compact space,
for the weak topology it inherits from the probability measures on the product. -/
instance Coupling.instCompactSpace [CompleteSpace X] [CompleteSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} : CompactSpace (Coupling μ ν) :=
  isCompact_iff_compactSpace.mp (isCompact_setOfPred_isCoupling_of_completeSpace μ ν)

end Compact

end TauCeti
