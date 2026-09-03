/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
public import TauCeti.MeasureTheory.OptimalTransport.Compactness
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic
-- Proof-only: continuity of `ENNReal.rpow` in its base, for the `p`-Wasserstein cost.
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Existence of an optimal transport plan

The primal Kantorovich problem minimises `π ↦ ∫⁻ z, c z ∂π` over the couplings of two fixed
probability measures. This file proves that the minimum is attained for a lower semicontinuous
cost: the infimum defining `TauCeti.transportCost` is a minimum, realised by a plan satisfying
`TauCeti.IsOptimalCoupling`.

The proof is the direct method of the calculus of variations, with both of its ingredients already
isolated. The feasible set is weakly compact and nonempty
(`TauCeti.isCompact_setOfPred_isCoupling`, the product plan), and the objective is weakly lower
semicontinuous (`TauCeti.lowerSemicontinuous_lintegral_probabilityMeasure`); a lower semicontinuous
function on a nonempty compact set attains its infimum.

Nothing here needs the minimum to be finite. If every plan has infinite cost — which happens, for
instance, when `c` is `∞` off the diagonal and the two marginals are mutually singular — the
theorem still produces an optimal plan, of cost `∞`; the statement separates existence from
finiteness, as the roadmap asks.

The cost is only assumed lower semicontinuous, not continuous, and this is the point: the costs of
interest, such as `edist` raised to a power or the `{0, ∞}`-valued indicator of a closed constraint
set, are lower semicontinuous, and lower semicontinuity is exactly what guarantees attainment of
the infimum on the compact set of couplings.

## Main statements

* `TauCeti.exists_isOptimalCoupling_of_isTightMeasureSet` — an optimal plan exists whenever both
  marginals are tight;
* `TauCeti.exists_isOptimalCoupling` — its Polish specialisation, where tightness is automatic;
* `TauCeti.exists_coupling_isOptimalCoupling` — the same statement with the plan delivered as an
  element of the bundled type `TauCeti.Coupling`;
* `TauCeti.isCompact_setOfPred_isOptimalCoupling` — the optimal plans themselves form a weakly
  compact set;
* `TauCeti.transportCost_iSup_eq_iSup` — minimization over compact coupling sets commutes with an
  increasing supremum of lower-semicontinuous costs;
* `TauCeti.transportCost_eq_iSup_transportCost_lscApprox` — transport cost commutes with the
  canonical monotone approximation of a lower-semicontinuous cost;
* `TauCeti.exists_isOptimalCoupling_edist` and `TauCeti.exists_isOptimalCoupling_edist_rpow` — the
  acceptance instances: the Kantorovich–Rubinstein cost `edist`, and the `p`-Wasserstein cost
  `edist ^ p`, admit optimal plans on a Polish space.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 4.1 — existence of an
  optimal coupling for a lower semicontinuous cost on Polish spaces.
* C. Villani, *Topics in Optimal Transportation*, AMS 2003, Theorem 1.3.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Springer 2015, Chapter 1 — the
  direct method for the Kantorovich problem.

This is Layer 1, item 5 of the optimal-transport roadmap.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section Tight

/-! The two factors are Borel metrizable spaces, one of the two second countable — the hypotheses
under which the product is a Borel space and the coupling set is weakly compact. Metrizability is
asked of the topology, not of a chosen distance, so a space known only to be Polish qualifies; the
pseudometric that the direct method runs on is installed inside the proofs. -/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
  [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopologyEither X Y] {c : X × Y → ℝ≥0∞}

/-- **Primal attainment for a lower semicontinuous cost.** If both marginals are tight, the
transport cost of `μ` and `ν` is attained: some coupling `π` satisfies
`∫⁻ z, c z ∂π = transportCost c μ ν`. No finiteness is assumed or concluded — the optimal value may
be `∞`. -/
theorem exists_isOptimalCoupling_of_isTightMeasureSet {μ : Measure X} [IsProbabilityMeasure μ]
    {ν : Measure Y} [IsProbabilityMeasure ν] (hμ : IsTightMeasureSet {μ})
    (hν : IsTightMeasureSet {ν}) (hc : LowerSemicontinuous c) :
    ∃ π, IsOptimalCoupling c π μ ν := by
  -- The direct method is run by `TauCeti.exists_isMinOn_lintegral`, which asks the underlying
  -- space for a pseudometric; metrizability of the two factors supplies one on the product.
  let : PseudoMetricSpace (X × Y) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X × Y)
  have hKne : {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ ν}.Nonempty :=
    ⟨(Coupling.prod ⟨μ, ‹_›⟩ ⟨ν, ‹_›⟩).1, (Coupling.prod ⟨μ, ‹_›⟩ ⟨ν, ‹_›⟩).2⟩
  obtain ⟨π, hπK, hπmin⟩ := exists_isMinOn_lintegral hKne
    (isCompact_setOfPred_isCoupling (μ := ⟨μ, ‹_›⟩) (ν := ⟨ν, ‹_›⟩) hμ hν) hc
  refine ⟨π.toMeasure, isOptimalCoupling_iff.mpr ⟨hπK, fun σ hσ ↦ ?_⟩⟩
  have hσprob : IsProbabilityMeasure σ := hσ.isProbabilityMeasure
  exact isMinOn_iff.mp hπmin ⟨σ, hσprob⟩ hσ

/-- **The optimal plans form a compact set.** An optimal plan is a coupling whose cost is at most
the transport cost, the reverse inequality being automatic; so the optimal set is the intersection
of the compact set of couplings with a weakly closed sublevel set of the cost functional. Together
with `TauCeti.exists_isOptimalCoupling_of_isTightMeasureSet`, which makes it nonempty, this is the
compactness a selection argument runs on. -/
theorem isCompact_setOfPred_isOptimalCoupling {μ : Measure X} [IsProbabilityMeasure μ]
    {ν : Measure Y} [IsProbabilityMeasure ν] (hμ : IsTightMeasureSet {μ})
    (hν : IsTightMeasureSet {ν}) (hc : LowerSemicontinuous c) :
    IsCompact {π : ProbabilityMeasure (X × Y) | IsOptimalCoupling c π.toMeasure μ ν} := by
  have hset : {π : ProbabilityMeasure (X × Y) | IsOptimalCoupling c π.toMeasure μ ν} =
      {π : ProbabilityMeasure (X × Y) | IsCoupling π.toMeasure μ ν} ∩
        {π : ProbabilityMeasure (X × Y) | ∫⁻ z, c z ∂π.toMeasure ≤ transportCost c μ ν} := by
    ext π
    exact ⟨fun h ↦ ⟨h.toIsCoupling, h.lintegral_eq.le⟩,
      fun h ↦ ⟨h.1, le_antisymm h.2 (transportCost_le_lintegral h.1 c)⟩⟩
  rw [hset]
  -- The sublevel set is closed by `TauCeti.isClosed_setOfPred_lintegral_le_probabilityMeasure`,
  -- which asks the underlying space for a pseudometric; metrizability of the two factors supplies
  -- one on the product.
  let : PseudoMetricSpace (X × Y) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X × Y)
  exact (isCompact_setOfPred_isCoupling (μ := ⟨μ, ‹_›⟩) (ν := ⟨ν, ‹_›⟩) hμ hν).inter_right
    (isClosed_setOfPred_lintegral_le_probabilityMeasure hc _)

end Tight

section CompactMetrizable

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
  [TopologicalSpace.MetrizableSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Monotone convergence of optimal transport costs on compact spaces.** The transport cost of
the pointwise supremum of an increasing sequence of lower-semicontinuous costs is the supremum of
their transport costs. No finiteness assumption is made: both sides may be `∞`.

Compactness of the feasible set is load-bearing. Without it, an escaping sequence of approximate
minimizers can make the supremum of the minima strictly smaller than the minimum of the supremum. -/
theorem transportCost_iSup_eq_iSup {cs : ℕ → X × Y → ℝ≥0∞}
    (hcs : ∀ n, LowerSemicontinuous (cs n)) (hmono : Monotone cs) :
    transportCost (fun z ↦ ⨆ n, cs n z) μ ν = ⨆ n, transportCost (cs n) μ ν := by
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  let : PseudoMetricSpace Y := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Y
  let a : ℝ≥0∞ := ⨆ n : ℕ, transportCost (cs n) μ ν
  let K : ℕ → Set (ProbabilityMeasure (X × Y)) := fun n ↦
    {π | IsCoupling π.toMeasure μ ν} ∩
      {π | ∫⁻ z, cs n z ∂π.toMeasure ≤ a}
  have ha_le : a ≤ transportCost (fun z ↦ ⨆ n, cs n z) μ ν := by
    refine iSup_le fun n ↦ transportCost_mono (fun z ↦ le_iSup (fun m ↦ cs m z) n)
  suffices transportCost (fun z ↦ ⨆ n, cs n z) μ ν ≤ a by
    exact le_antisymm this ha_le
  have hK_nonempty (n : ℕ) : (K n).Nonempty := by
    obtain ⟨π, hπ⟩ := exists_isOptimalCoupling_of_isTightMeasureSet
      (μ := μ) (ν := ν) IsTightMeasureSet.of_compactSpace
      IsTightMeasureSet.of_compactSpace (hcs n)
    let π' : ProbabilityMeasure (X × Y) := ⟨π, hπ.toIsCoupling.isProbabilityMeasure⟩
    refine ⟨π', hπ.toIsCoupling, ?_⟩
    -- `π'` only bundles the raw optimal plan `π`; expose that coercion to use its optimal value.
    change (∫⁻ z, cs n z ∂π) ≤ a
    exact hπ.lintegral_eq.trans_le (le_iSup (fun m : ℕ ↦ transportCost (cs m) μ ν) n)
  have hK_succ (n : ℕ) : K (n + 1) ⊆ K n := by
    rintro π ⟨hπ, hπcost⟩
    refine ⟨hπ, hπcost.trans' (lintegral_mono fun z ↦ ?_)⟩
    exact hmono (Nat.le_succ n) z
  have hK_closed (n : ℕ) : IsClosed (K n) := by
    exact (isClosed_setOfPred_isCoupling_of_compactSpace
      (⟨μ, ‹IsProbabilityMeasure μ›⟩ : ProbabilityMeasure X)
      (⟨ν, ‹IsProbabilityMeasure ν›⟩ : ProbabilityMeasure Y)).inter
        (isClosed_setOfPred_lintegral_le_probabilityMeasure (hcs n) a)
  have hK_compact : IsCompact (K 0) :=
    (isCompact_setOfPred_isCoupling_of_compactSpace
      (⟨μ, ‹IsProbabilityMeasure μ›⟩ : ProbabilityMeasure X)
      (⟨ν, ‹IsProbabilityMeasure ν›⟩ : ProbabilityMeasure Y)).inter_right
        (isClosed_setOfPred_lintegral_le_probabilityMeasure (hcs 0) a)
  obtain ⟨π, hπ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K hK_succ hK_nonempty hK_compact hK_closed
  have hπK : ∀ n, π ∈ K n := Set.mem_iInter.1 hπ
  refine (transportCost_le_lintegral (hπK 0).1 (fun z ↦ ⨆ n, cs n z)).trans ?_
  rw [lintegral_iSup (fun n ↦ (hcs n).measurable) hmono]
  exact iSup_le fun n ↦ (hπK n).2

end CompactMetrizable

section CompactPseudoMetric

variable {X Y : Type*} [PseudoMetricSpace X] [T0Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [PseudoMetricSpace Y] [T0Space Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} {ν : Measure Y}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c : X × Y → ℝ≥0∞}

/-- On compact metrizable spaces, the transport costs of the canonical bounded-continuous
approximations of a lower-semicontinuous cost increase to the transport cost of the original
cost. This is the minimization counterpart of
`TauCeti.lintegral_eq_iSup_lintegral_lscApprox`. -/
theorem transportCost_eq_iSup_transportCost_lscApprox (hc : LowerSemicontinuous c) :
    transportCost c μ ν =
      ⨆ n : ℕ, transportCost (fun z ↦ (lscApprox c n z : ℝ≥0∞)) μ ν := by
  simpa only [iSup_coe_lscApprox hc] using
    transportCost_iSup_eq_iSup
      (cs := fun n z ↦ (lscApprox c n z : ℝ≥0∞))
      (fun n ↦ (ENNReal.continuous_coe.comp (lscApprox c n).continuous).lowerSemicontinuous)
      (monotone_coe_lscApprox c)

end CompactPseudoMetric

section Polish

/-! The Polish specialisation is stated for Mathlib's `PolishSpace`, the topological notion: second
countable and completely metrizable, with no distance chosen. -/

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y] {c : X × Y → ℝ≥0∞}

/-- **Primal attainment on Polish spaces.** Every finite Borel measure on a Polish space is tight,
so a lower semicontinuous cost always admits an optimal transport plan between two probability
measures there. -/
theorem exists_isOptimalCoupling (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y)
    [IsProbabilityMeasure ν] (hc : LowerSemicontinuous c) :
    ∃ π, IsOptimalCoupling c π μ ν :=
  exists_isOptimalCoupling_of_isTightMeasureSet isTightMeasureSet_singleton
    isTightMeasureSet_singleton hc

/-- Primal attainment with the optimal plan delivered inside the bundled coupling type, which is
the domain the probability transport problem is optimised over. -/
theorem exists_coupling_isOptimalCoupling (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (hc : LowerSemicontinuous c) :
    ∃ π : Coupling μ ν,
      IsOptimalCoupling c (π : ProbabilityMeasure (X × Y)).toMeasure μ.toMeasure ν.toMeasure := by
  have hμ : IsProbabilityMeasure μ.toMeasure := μ.2
  have hν : IsProbabilityMeasure ν.toMeasure := ν.2
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling μ.toMeasure ν.toMeasure hc
  have hπprob : IsProbabilityMeasure π := hπ.toIsCoupling.isProbabilityMeasure
  exact ⟨⟨⟨π, hπprob⟩, hπ.toIsCoupling⟩, hπ⟩

/-- The acceptance instance: on a Polish space the Kantorovich–Rubinstein cost `edist`, which is
continuous and hence lower semicontinuous, admits an optimal transport plan between any two
probability measures. -/
theorem exists_isOptimalCoupling_edist {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ π, IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2) π μ ν :=
  exists_isOptimalCoupling μ ν continuous_edist.lowerSemicontinuous

/-- The cost `edist ^ p` underlying the `p`-Wasserstein distance admits an optimal transport plan
on a Polish space. The exponent is unrestricted because `ENNReal.rpow` is continuous for every real
exponent; the case the Wasserstein distances use is `1 ≤ p`. -/
theorem exists_isOptimalCoupling_edist_rpow {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (p : ℝ) :
    ∃ π, IsOptimalCoupling (fun z : X × X ↦ edist z.1 z.2 ^ p) π μ ν :=
  exists_isOptimalCoupling μ ν
    ((ENNReal.continuous_rpow_const.comp continuous_edist).lowerSemicontinuous)

end Polish

end TauCeti
