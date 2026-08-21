/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.MetricSpace.Polish
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
the `T1Space` hypothesis carried here. Mathlib derives it from
`MeasureTheory.ProbabilityMeasure.t2Space`, whose hypotheses are `BorelSpace` together with
`HasOuterApproxClosed` — so it is available on the metrizable factors the later sections work
with, but is asked for explicitly here rather than assumed.

*Compactness* is Prokhorov's theorem. Tightness of the coupling set follows from tightness of the
two marginals alone: a compact rectangle `K₁ ×ˢ K₂` misses at most the mass its two sides miss,
uniformly over all couplings, because every coupling has the same two marginals. Tightness is
therefore stated for arbitrary measures with tight marginals, and the topological hypotheses enter
only when Prokhorov's theorem is applied.

## Main statements

* `TauCeti.isClosed_setOfPred_isCoupling` — the couplings of `μ` and `ν` are a weakly closed set of
  probability measures on the product, with canonical Polish and compact-metrizable
  specialisations;
* `TauCeti.isTightMeasureSet_setOfPred_isCoupling` — the couplings of two tight measures form a
  tight family, with no topological hypothesis beyond the two topologies themselves;
* `TauCeti.isCompact_setOfPred_isCoupling_of_prokhorov` — the abstract compactness theorem for a
  product on which tight families of probability measures have compact closure;
* `TauCeti.isCompact_setOfPred_isCoupling` — the Prokhorov theorem for Hausdorff Borel factors,
  with compact-metrizable and Polish specialisations;
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

section Closed

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopologyEither X Y]

/-- **The couplings of two probability measures are weakly closed.** The coupling set is the
intersection of the preimages of `{μ}` and `{ν}` under the two marginal maps, both of which are
continuous for the topology of convergence in distribution. The `T1Space` hypotheses are what make
the two singletons closed; they hold whenever the two factors are `HasOuterApproxClosed` — in
particular whenever they are metrizable — since the spaces of probability measures are then
Hausdorff by `MeasureTheory.ProbabilityMeasure.t2Space`. -/
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

section AbstractCompact

/-! The abstract theorem exposes exactly the Prokhorov property used by the coupling argument:
every tight family of probability measures on the product has compact closure. -/

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T1Space (ProbabilityMeasure X)] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T1Space (ProbabilityMeasure Y)] [SecondCountableTopologyEither X Y]

/-- **Compactness of couplings under an abstract Prokhorov property.** If every tight family of
probability measures on the product has compact closure, then the couplings of two tight marginals
form a compact set. This keeps the compactness argument available beyond the concrete Hausdorff
Borel version of Prokhorov's theorem without inferring the property from Radon regularity. -/
theorem isCompact_setOfPred_isCoupling_of_prokhorov
    (hprokhorov : ∀ S : Set (ProbabilityMeasure (X × Y)),
      IsTightMeasureSet {((π : ProbabilityMeasure (X × Y)).toMeasure) | π ∈ S} →
        IsCompact (closure S))
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (hμ : IsTightMeasureSet {μ.toMeasure}) (hν : IsTightMeasureSet {ν.toMeasure}) :
    IsCompact
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} := by
  have hclosed := isClosed_setOfPred_isCoupling μ ν
  have htight : IsTightMeasureSet {(π : ProbabilityMeasure (X × Y)).toMeasure |
      π ∈ {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure}} := by
    refine (isTightMeasureSet_setOfPred_isCoupling hμ hν).subset ?_
    rintro - ⟨π, hπ, rfl⟩
    exact hπ
  simpa only [hclosed.closure_eq] using hprokhorov _ htight

end AbstractCompact

section Compact

/-! Prokhorov's theorem asks the underlying space to be Hausdorff and Borel. Closedness of the
coupling set additionally asks that the two spaces of probability measures be `T1`; these are the
hypotheses exposed below, without choosing a metric on either factor. -/

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [T1Space (ProbabilityMeasure X)]
  [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
  [T1Space (ProbabilityMeasure Y)] [SecondCountableTopologyEither X Y]

/-- **The couplings of two tight probability measures are weakly compact.** The set is tight by
`TauCeti.isTightMeasureSet_setOfPred_isCoupling`, hence relatively compact by Prokhorov's theorem,
and it is closed by `TauCeti.isClosed_setOfPred_isCoupling`; so it equals its own closure and is
compact. -/
theorem isCompact_setOfPred_isCoupling {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}
    (hμ : IsTightMeasureSet {μ.toMeasure}) (hν : IsTightMeasureSet {ν.toMeasure}) :
    IsCompact
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} := by
  exact isCompact_setOfPred_isCoupling_of_prokhorov
    (fun _ ↦ isCompact_closure_of_isTightMeasureSet) hμ hν

end Compact

section CompactMetrizable

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
  [TopologicalSpace.MetrizableSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Closedness of couplings on compact metrizable spaces.** This is the directly usable
compact-metrizable specialisation of `TauCeti.isClosed_setOfPred_isCoupling`. -/
theorem isClosed_setOfPred_isCoupling_of_compactSpace (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsClosed
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} := by
  let : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  let : UniformSpace Y := TopologicalSpace.pseudoMetrizableSpaceUniformity Y
  let : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.isSeparable_univ_iff.mp isCompact_univ.isSeparable
  let : TopologicalSpace.SeparableSpace Y :=
    TopologicalSpace.isSeparable_univ_iff.mp isCompact_univ.isSeparable
  exact isClosed_setOfPred_isCoupling μ ν

/-- **Compactness of couplings on compact metrizable spaces.** Compactness makes every family of
measures tight, so the general coupling compactness theorem applies without marginal hypotheses. -/
theorem isCompact_setOfPred_isCoupling_of_compactSpace (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsCompact
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} := by
  let : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  let : UniformSpace Y := TopologicalSpace.pseudoMetrizableSpaceUniformity Y
  let : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.isSeparable_univ_iff.mp isCompact_univ.isSeparable
  let : TopologicalSpace.SeparableSpace Y :=
    TopologicalSpace.isSeparable_univ_iff.mp isCompact_univ.isSeparable
  exact isCompact_setOfPred_isCoupling IsTightMeasureSet.of_compactSpace
    IsTightMeasureSet.of_compactSpace

end CompactMetrizable

section Polish

/-! The Polish specialisation is stated for Mathlib's `PolishSpace`, the topological notion: second
countable and completely metrizable, with no distance chosen. That is what makes the two factors
tight and hence the coupling set compact. -/

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **Closedness of couplings on Polish Borel spaces.** This is the canonical weak/Borel
specialisation: the probability-measure spaces are Hausdorff, so the two marginal fibers are
closed. -/
theorem isClosed_setOfPred_isCoupling_of_polishSpace (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsClosed
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} :=
  isClosed_setOfPred_isCoupling μ ν

/-- **The couplings of two probability measures on Polish spaces are weakly compact.** On a Polish
space every finite Borel measure is tight, so the tightness hypotheses of
`TauCeti.isCompact_setOfPred_isCoupling` are automatic. This is the compactness that the direct
method of the calculus of variations consumes. -/
theorem isCompact_setOfPred_isCoupling_of_polishSpace (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) :
    IsCompact
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} :=
  isCompact_setOfPred_isCoupling isTightMeasureSet_singleton isTightMeasureSet_singleton

/-- The bundled type of couplings of two probability measures on Polish spaces is a compact space,
for the weak topology it inherits from the probability measures on the product. -/
instance Coupling.instCompactSpace {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} :
    CompactSpace (Coupling μ ν) :=
  isCompact_iff_compactSpace.mp (isCompact_setOfPred_isCoupling_of_polishSpace μ ν)

end Polish

end TauCeti
