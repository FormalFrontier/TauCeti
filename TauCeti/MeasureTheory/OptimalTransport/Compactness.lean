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

Both halves are then run with *moving* marginals: a family of plans that is eventually feasible for
two tight families of marginals is relatively compact, and each of its weak limits along a finer
filter is a coupling of the limiting marginals. Nothing about a cost function enters, which is why
this lives here rather than in the stability file that consumes it.

## Main statements

* `TauCeti.isClosed_setOfPred_isCoupling` — the couplings of `μ` and `ν` are a weakly closed set of
  probability measures on the product, with canonical Polish and compact-metrizable
  specialisations;
* `TauCeti.isTightMeasureSet_setOfPred_exists_isCoupling` and
  `TauCeti.isTightMeasureSet_setOfPred_isCoupling` — the couplings of two tight families of
  measures, and of two tight measures, form a tight family, with no topological hypothesis beyond
  the two topologies themselves;
* `TauCeti.isCompact_setOfPred_isCoupling_of_prokhorov` — the abstract compactness theorem for a
  product on which tight families of probability measures have compact closure;
* `TauCeti.isCompact_setOfPred_isCoupling` — the Prokhorov theorem for Hausdorff Borel factors,
  with compact-metrizable and Polish specialisations;
* `TauCeti.isCoupling_of_tendsto` — the coupling constraint passes to weak limits when the
  marginals converge;
* `TauCeti.exists_isCoupling_tendsto_of_isTightMeasureSet` — relative compactness of a family of
  plans with tight varying marginals;
* `TauCeti.Coupling.instCompactSpace` — the bundled coupling type is a compact space.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 4 — the tightness lemma for
  transference plans that precedes the existence theorem for an optimal coupling.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Springer 2015, Chapter 1 — the
  same compactness argument, run through Prokhorov's theorem.

This is Layer 1, items 2 and 3 of the optimal-transport roadmap, with the moving-marginal
compactness used by item 6.
-/

public section

open Filter MeasureTheory Set
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
  have hset : {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ.toMeasure ν.toMeasure} =
      (fun π : ProbabilityMeasure (X × Y) ↦ π.map Prod.fst) ⁻¹' {μ} ∩
        (fun π : ProbabilityMeasure (X × Y) ↦ π.map Prod.snd) ⁻¹' {ν} := by
    ext π
    simpa only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff] using
      isCoupling_toMeasure_iff
  rw [hset]
  exact (isClosed_singleton.preimage
      (ProbabilityMeasure.continuous_map (f := (Prod.fst : X × Y → X)) continuous_fst)).inter
    (isClosed_singleton.preimage
      (ProbabilityMeasure.continuous_map (f := (Prod.snd : X × Y → Y)) continuous_snd))

end Closed

section Tight

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y]
  [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

/-- **The couplings of two tight families of measures form a tight family.** A coupling gives the
complement of a compact rectangle at most the mass its two marginals give the complements of the
two sides, and those bounds are uniform over the two families because a coupling is exhausted by
its marginals. No hypothesis beyond the two topologies is needed. The marginals are allowed to
range over sets rather than to be fixed, which is what a stability argument with moving marginals
consumes. -/
theorem isTightMeasureSet_setOfPred_exists_isCoupling {S : Set (Measure X)} {T : Set (Measure Y)}
    (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T) :
    IsTightMeasureSet {π : Measure (X × Y) | ∃ μ ∈ S, ∃ ν ∈ T, IsCoupling π μ ν} := by
  refine IsTightMeasureSet.prodMk (hS.subset ?_) (hT.subset ?_)
  · rintro - ⟨π, ⟨μ, hμ, ν, -, hπ⟩, rfl⟩
    rwa [hπ.fst_eq]
  · rintro - ⟨π, ⟨μ, -, ν, hν, hπ⟩, rfl⟩
    rwa [hπ.snd_eq]

/-- **The couplings of two tight measures form a tight family.** This is the fixed-marginal case of
`TauCeti.isTightMeasureSet_setOfPred_exists_isCoupling`, and it is the tightness that Prokhorov's
theorem is applied to below. -/
theorem isTightMeasureSet_setOfPred_isCoupling (hμ : IsTightMeasureSet {μ})
    (hν : IsTightMeasureSet {ν}) :
    IsTightMeasureSet {π : Measure (X × Y) | IsCoupling π μ ν} :=
  (isTightMeasureSet_setOfPred_exists_isCoupling hμ hν).subset fun _ hπ ↦ ⟨μ, rfl, ν, rfl, hπ⟩

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

section MovingMarginals

/-! Weak limits of plans whose marginals move. The hypotheses are those of the two sections above,
strengthened from `T1` to `T2` on the two spaces of marginals because a limit is identified here,
not merely trapped in a closed set. -/

variable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space (ProbabilityMeasure X)] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T2Space (ProbabilityMeasure Y)] [SecondCountableTopologyEither X Y] {l : Filter ι}
  {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y} {μ : ProbabilityMeasure X}
  {ν : ProbabilityMeasure Y} {πs : ι → ProbabilityMeasure (X × Y)}
  {π : ProbabilityMeasure (X × Y)}

/-- **The coupling constraint passes to weak limits.** If the plans `πs i` are eventually couplings
of `μs i` and `νs i`, and the plans and both marginals converge weakly along the same filter,
then the limiting plan is a coupling of the limiting marginals.
The two marginal maps are weakly continuous, so this is uniqueness of weak limits applied to the
two marginals of `πs`. -/
theorem isCoupling_of_tendsto [l.NeBot]
    (hπs : ∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure)
    (hπ : Tendsto πs l (𝓝 π)) (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) :
    IsCoupling π.toMeasure μ.toMeasure ν.toMeasure := by
  refine isCoupling_toMeasure_iff.mpr ⟨?_, ?_⟩
  · have h₁ : Tendsto (fun i ↦ (πs i).map Prod.fst) l
        (𝓝 (π.map Prod.fst)) :=
      ((ProbabilityMeasure.continuous_map (f := (Prod.fst : X × Y → X))
        continuous_fst).tendsto π).comp hπ
    refine tendsto_nhds_unique h₁ (hμ.congr' ?_)
    exact hπs.mono fun i hi ↦ (isCoupling_toMeasure_iff.mp hi).1.symm
  · have h₂ : Tendsto (fun i ↦ (πs i).map Prod.snd) l
        (𝓝 (π.map Prod.snd)) :=
      ((ProbabilityMeasure.continuous_map (f := (Prod.snd : X × Y → Y))
        continuous_snd).tendsto π).comp hπ
    refine tendsto_nhds_unique h₂ (hν.congr' ?_)
    exact hπs.mono fun i hi ↦ (isCoupling_toMeasure_iff.mp hi).2.symm

/-- **Relative compactness of a family of transport plans with moving marginals.** If a tail of
each marginal family is tight, then any eventually feasible family of plans has a weakly convergent
refinement whose limit is a coupling of the limiting marginals. -/
theorem exists_isCoupling_tendsto_of_isTightMeasureSet [T2Space X] [T2Space Y]
    (hμt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (μs i).toMeasure) '' s))
    (hνt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (νs i).toMeasure) '' s))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) [l.NeBot]
    (hπs : ∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure) :
    ∃ (l'' : Filter ι) (π : ProbabilityMeasure (X × Y)), l''.NeBot ∧ l'' ≤ l ∧
      Tendsto πs l'' (𝓝 π) ∧ IsCoupling π.toMeasure μ.toMeasure ν.toMeasure := by
  obtain ⟨s, hs, hμs⟩ := hμt
  obtain ⟨t, ht, hνt⟩ := hνt
  set S : Set (ProbabilityMeasure (X × Y)) :=
    {σ | ∃ i ∈ s ∩ t, IsCoupling σ.toMeasure (μs i).toMeasure (νs i).toMeasure}
  have htight : IsTightMeasureSet {(σ : ProbabilityMeasure (X × Y)).toMeasure | σ ∈ S} := by
    refine (isTightMeasureSet_setOfPred_exists_isCoupling hμs hνt).subset ?_
    rintro - ⟨σ, ⟨i, hi, hσ⟩, rfl⟩
    exact ⟨(μs i).toMeasure, ⟨i, hi.1, rfl⟩, (νs i).toMeasure, ⟨i, hi.2, rfl⟩, hσ⟩
  have hcompact : IsCompact (closure S) := isCompact_closure_of_isTightMeasureSet htight
  have hmem : ∀ᶠ i in l, πs i ∈ closure S := by
    filter_upwards [hπs, inter_mem hs ht] with i hi hit
    have hiS : πs i ∈ S := ⟨i, hit, hi⟩
    exact subset_closure hiS
  obtain ⟨π, -, hπ⟩ := hcompact.exists_mapClusterPt_of_frequently
    hmem.frequently
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hπ
  exact ⟨U, π, U.neBot, hUle, hUtend, isCoupling_of_tendsto
    (hπs.filter_mono hUle) hUtend (hμ.mono_left hUle) (hν.mono_left hUle)⟩

end MovingMarginals

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
