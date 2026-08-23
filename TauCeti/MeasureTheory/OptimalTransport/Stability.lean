/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
public import TauCeti.MeasureTheory.OptimalTransport.Compactness
public import TauCeti.MeasureTheory.OptimalTransport.Cost
-- Proof-only: Prokhorov's theorem in both directions, and the order-topology criterion turning a
-- `liminf`/`limsup` sandwich into convergence.
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Stability of the primal transport problem under varying marginals and costs

A family of transport problems indexed by a filter is *stable* when its optimal values converge to
the optimal value of a limiting problem, and its optimal plans accumulate only on optimal plans of
that limiting problem. This file proves both, from two hypotheses that are stated explicitly rather
than packaged: a lower bound on the asymptotic cost of weakly convergent feasible families
(`TauCeti.IsCostLiminfStable`), and an upper bound produced by approximating each limiting plan
(`TauCeti.HasRecoveryPlans`).

The two hypotheses do exactly one job each, and neither implies the other.

`TauCeti.IsCostLiminfStable` is what makes the limiting value a *lower* bound: it says that along
any finer filter, a weakly convergent family of feasible plans cannot lose cost in the limit. It
holds for free when the limiting cost is lower semicontinuous and is dominated by the family
(`TauCeti.isCostLiminfStable_of_le`), which covers the fixed-cost problem where only the marginals
move.

`TauCeti.HasRecoveryPlans` is what makes the limiting value an *upper* bound: every plan of the
limiting problem must be reachable, asymptotically and in cost, by feasible plans of the moving
problems. It is a genuine assumption — for a fixed lower semicontinuous cost and weakly converging
marginals the optimal values can strictly drop in the limit: take `c` to be the indicator of the
off-diagonal of `ℝ × ℝ`, which is lower semicontinuous, `μs n = δ (1 / (n + 1))` and `νs n = δ 0`;
every moving problem then has value `1`, while the limiting problem has value `0`. Note that the
weak convergence of a recovery family is never used, only its asymptotic cost, so it is not
required.

The two bounds are separated on purpose: `TauCeti.transportCost_le_liminf_transportCost` needs the
liminf hypothesis and compactness, `TauCeti.limsup_transportCost_le_transportCost` needs the
recovery hypothesis and nothing else, and only `TauCeti.tendsto_transportCost` needs both.

Compactness enters through `TauCeti.exists_isCoupling_tendsto_of_isTightMeasureSet`: a family of
plans whose (varying) marginals form two tight families is relatively compact, and every weak limit
of it along a finer filter is a coupling of the limiting marginals. This is the "tightness of
optimizer subsequences" step, and it is what lets the arguments run along a filter rather than a
sequence: passing to a subsequence is replaced by passing to a finer filter.

## Main statements

* `TauCeti.isCoupling_of_tendsto` — the coupling constraint passes to weak limits when the
  marginals converge;
* `TauCeti.IsCostLiminfStable` and `TauCeti.HasRecoveryPlans` — the two stability hypotheses, with
  `TauCeti.isCostLiminfStable_of_le` and `TauCeti.isCostLiminfStable_const` supplying the first one
  from lower semicontinuity;
* `TauCeti.exists_isCoupling_tendsto_of_isTightMeasureSet` — relative compactness of a family of
  plans with tight varying marginals;
* `TauCeti.transportCost_le_liminf_transportCost` and
  `TauCeti.limsup_transportCost_le_transportCost` — the two one-sided bounds on the optimal values;
* `TauCeti.hasRecoveryPlans_of_limsup_le` — the recovery hypothesis for a family with fixed
  marginals;
* `TauCeti.tendsto_transportCost` — convergence of the optimal values, with
  `TauCeti.tendsto_transportCost_of_const_marginals` as a directly checkable instance;
* `TauCeti.isOptimalCoupling_of_tendsto` and `TauCeti.exists_isOptimalCoupling_tendsto` —
  subsequential convergence of optimal plans to an optimal plan of the limiting problem;
* `TauCeti.transportCost_le_liminf_transportCost_of_lowerSemicontinuous` — the fixed-cost
  corollary: on Polish spaces the optimal transport cost of a lower semicontinuous cost is weakly
  lower semicontinuous in the pair of marginals.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 5.20 — stability of optimal
  transport: convergence of the optimal costs and of the optimal plans under weakly converging
  marginals and uniformly converging costs.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Springer 2015, Section 1.2 —
  the same statement obtained by the direct method from tightness and lower semicontinuity.

This is Layer 1, item 6 of the optimal-transport roadmap. Layer 10 is where these two hypotheses
are packaged as the Γ-liminf, Γ-limsup and equicoercivity conditions of an abstract variational
convergence; here they stay explicit.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section Limit

/-! Weak limits of transport plans. The hypotheses are those of
`TauCeti.isClosed_setOfPred_isCoupling`, strengthened from `T1` to `T2` on the two spaces of
marginals because a limit is identified here, not merely trapped in a closed set. -/

variable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space (ProbabilityMeasure X)] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T2Space (ProbabilityMeasure Y)] [SecondCountableTopologyEither X Y] {l l' : Filter ι}
  {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y} {μ : ProbabilityMeasure X}
  {ν : ProbabilityMeasure Y} {πs : ι → ProbabilityMeasure (X × Y)}
  {π : ProbabilityMeasure (X × Y)}

/-- **The coupling constraint passes to weak limits.** If the plans `πs i` are eventually couplings
of `μs i` and `νs i` along a filter `l'` refining `l`, and both the marginals along `l` and the
plans along `l'` converge weakly, then the limiting plan is a coupling of the limiting marginals.
The two marginal maps are weakly continuous, so this is uniqueness of weak limits applied to the
two marginals of `πs`. -/
theorem isCoupling_of_tendsto [l'.NeBot] (hl' : l' ≤ l)
    (hπs : ∀ᶠ i in l', IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure)
    (hπ : Tendsto πs l' (𝓝 π)) (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) :
    IsCoupling π.toMeasure μ.toMeasure ν.toMeasure := by
  have hfst : Continuous fun σ : ProbabilityMeasure (X × Y) ↦ σ.map measurable_fst.aemeasurable :=
    ProbabilityMeasure.continuous_map (f := (Prod.fst : X × Y → X)) continuous_fst
  have hsnd : Continuous fun σ : ProbabilityMeasure (X × Y) ↦ σ.map measurable_snd.aemeasurable :=
    ProbabilityMeasure.continuous_map (f := (Prod.snd : X × Y → Y)) continuous_snd
  refine isCoupling_toMeasure_iff.mpr ⟨?_, ?_⟩
  · have h₁ : Tendsto (fun i ↦ (πs i).map measurable_fst.aemeasurable) l'
        (𝓝 (π.map measurable_fst.aemeasurable)) := (hfst.tendsto π).comp hπ
    refine tendsto_nhds_unique h₁ ((hμ.mono_left hl').congr' ?_)
    exact hπs.mono fun i hi ↦ (isCoupling_toMeasure_iff.mp hi).1.symm
  · have h₂ : Tendsto (fun i ↦ (πs i).map measurable_snd.aemeasurable) l'
        (𝓝 (π.map measurable_snd.aemeasurable)) := (hsnd.tendsto π).comp hπ
    refine tendsto_nhds_unique h₂ ((hν.mono_left hl').congr' ?_)
    exact hπs.mono fun i hi ↦ (isCoupling_toMeasure_iff.mp hi).2.symm

end Limit

section Hypotheses

/-! The two stability hypotheses. Both are recorded as one-field structures so that they can be
consumed by name and produced by `refine ⟨fun ... ↦ ?_⟩`. -/

/-- The asymptotic lower bound half of stability: along every filter `l'` refining `l`, a weakly
convergent family of plans that is eventually feasible for the moving marginals `μs`, `νs` costs at
least the limiting cost `c` of its limit, asymptotically. Quantifying over the refinements of `l`
is what makes the hypothesis usable after passing to a convergent subfamily, exactly as the
classical statement quantifies over subsequences. -/
structure IsCostLiminfStable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopologyEither X Y] (l : Filter ι) (cs : ι → X × Y → ℝ≥0∞)
    (μs : ι → ProbabilityMeasure X) (νs : ι → ProbabilityMeasure Y) (c : X × Y → ℝ≥0∞) :
    Prop where
  /-- The cost of a weak limit of feasible plans is at most the asymptotic cost of the family. -/
  le_liminf {l' : Filter ι} (hne : l'.NeBot) (hle : l' ≤ l)
    {πs : ι → ProbabilityMeasure (X × Y)} {π : ProbabilityMeasure (X × Y)}
    (hπs : ∀ᶠ i in l', IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure)
    (hπ : Tendsto πs l' (𝓝 π)) :
    ∫⁻ z, c z ∂π.toMeasure ≤ liminf (fun i ↦ ∫⁻ z, cs i z ∂(πs i).toMeasure) l'

/-- The asymptotic upper bound half of stability: every plan of the limiting problem is recovered
by a family of plans that is eventually feasible for the moving marginals and costs no more,
asymptotically. Only the asymptotic cost of the recovery family is asked for; its weak convergence
back to the given plan is not used anywhere and is therefore not required. -/
structure HasRecoveryPlans {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopologyEither X Y] (l : Filter ι) (cs : ι → X × Y → ℝ≥0∞)
    (μs : ι → ProbabilityMeasure X) (νs : ι → ProbabilityMeasure Y) (c : X × Y → ℝ≥0∞)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : Prop where
  /-- Every coupling of the limiting marginals is approximated from above in cost. -/
  exists_recovery {π : ProbabilityMeasure (X × Y)}
    (hπ : IsCoupling π.toMeasure μ.toMeasure ν.toMeasure) :
    ∃ πs : ι → ProbabilityMeasure (X × Y),
      (∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure) ∧
        limsup (fun i ↦ ∫⁻ z, cs i z ∂(πs i).toMeasure) l ≤ ∫⁻ z, c z ∂π.toMeasure

end Hypotheses

section LowerSemicontinuous

/-! Lower semicontinuity of the limiting cost, together with domination by the family, is the
standard source of `TauCeti.IsCostLiminfStable`. The two factors are metrizable Borel spaces, one
of them second countable: the hypotheses under which the product carries a compatible pseudometric
and the weak-topology lower semicontinuity of
`TauCeti.lowerSemicontinuous_lintegral_probabilityMeasure` applies to it. -/

variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopologyEither X Y] {l : Filter ι}
  {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y} {cs : ι → X × Y → ℝ≥0∞}
  {c : X × Y → ℝ≥0∞}

/-- **A lower semicontinuous cost dominated by the family is liminf-stable.** Weak lower
semicontinuity of `π ↦ ∫⁻ c ∂π` gives the inequality for the limiting cost itself, and eventual
domination `c ≤ cs i` upgrades it to the moving costs. The feasibility of the plans plays no role:
the bound holds for every weakly convergent family. -/
theorem isCostLiminfStable_of_le (hc : LowerSemicontinuous c) (hcs : ∀ᶠ i in l, c ≤ cs i) :
    IsCostLiminfStable l cs μs νs c := by
  -- The lower semicontinuity theorem asks the underlying space for a pseudometric; metrizability
  -- of the two factors supplies one on the product.
  let : PseudoMetricSpace (X × Y) := TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X × Y)
  refine ⟨fun {l'} hne hle {πs} {π} _ hπ ↦ ?_⟩
  have := hne
  refine (le_liminf_lintegral_of_tendsto_probabilityMeasure hc hπ).trans (liminf_le_liminf ?_)
  exact (hcs.filter_mono hle).mono fun i hi ↦ lintegral_mono fun z ↦ hi z

/-- **A fixed lower semicontinuous cost is liminf-stable.** This is the case in which only the
marginals move; it is the hypothesis under which the optimal transport cost is weakly lower
semicontinuous in the marginals. -/
theorem isCostLiminfStable_const (hc : LowerSemicontinuous c) :
    IsCostLiminfStable l (fun _ ↦ c) μs νs c :=
  isCostLiminfStable_of_le hc (Eventually.of_forall fun _ ↦ le_rfl)

end LowerSemicontinuous

section Compact

/-! Relative compactness of a family of plans with moving marginals. The topological hypotheses are
those of `TauCeti.isCompact_setOfPred_isCoupling`, with `T2` on the two spaces of marginals so that
the limit is identified. -/

variable {ι X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [T2Space (ProbabilityMeasure X)] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] [T2Space (ProbabilityMeasure Y)] [SecondCountableTopologyEither X Y]
  {l l' : Filter ι} {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y}
  {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} {πs : ι → ProbabilityMeasure (X × Y)}

/-- **Relative compactness of a family of transport plans with moving marginals.** If the two
marginal families are tight, then any family of plans that is eventually feasible along `l'` has a
weakly convergent refinement, and its limit is a coupling of the limiting marginals.

This is the step that replaces the extraction of a convergent subsequence: the finer filter `l''`
plays the role of the subsequence, and it is produced from a cluster point of `πs` inside the
compact closure of the set of all plans with marginals in the two families. -/
theorem exists_isCoupling_tendsto_of_isTightMeasureSet
    (hμt : IsTightMeasureSet (Set.range fun i ↦ (μs i).toMeasure))
    (hνt : IsTightMeasureSet (Set.range fun i ↦ (νs i).toMeasure))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) [l'.NeBot] (hl' : l' ≤ l)
    (hπs : ∀ᶠ i in l', IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure) :
    ∃ (l'' : Filter ι) (π : ProbabilityMeasure (X × Y)), l''.NeBot ∧ l'' ≤ l' ∧
      Tendsto πs l'' (𝓝 π) ∧ IsCoupling π.toMeasure μ.toMeasure ν.toMeasure := by
  set S : Set (ProbabilityMeasure (X × Y)) :=
    {σ | ∃ i, IsCoupling σ.toMeasure (μs i).toMeasure (νs i).toMeasure}
  have htight : IsTightMeasureSet {(σ : ProbabilityMeasure (X × Y)).toMeasure | σ ∈ S} := by
    refine (isTightMeasureSet_setOfPred_isCoupling_of_mem hμt hνt).subset ?_
    rintro - ⟨σ, ⟨i, hi⟩, rfl⟩
    exact ⟨(μs i).toMeasure, mem_range_self i, (νs i).toMeasure, mem_range_self i, hi⟩
  have hcompact : IsCompact (closure S) := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨π, -, hπ⟩ := hcompact.exists_mapClusterPt_of_frequently
    (hπs.mono fun i hi ↦ subset_closure (show πs i ∈ S from ⟨i, hi⟩)).frequently
  have hne : (l' ⊓ comap πs (𝓝 π)).NeBot := by
    rw [neBot_inf_comap_iff_map, inf_comm]
    exact hπ
  have := hne
  have hconv : Tendsto πs (l' ⊓ comap πs (𝓝 π)) (𝓝 π) :=
    (map_mono inf_le_right).trans map_comap_le
  exact ⟨_, π, hne, inf_le_left, hconv, isCoupling_of_tendsto (l := l) (inf_le_left.trans hl')
    (hπs.filter_mono inf_le_left) hconv hμ hν⟩

end Compact

section Lower

/-! The lower bound on the optimal values: it is the half that consumes compactness. -/

variable {ι X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [T2Space (ProbabilityMeasure X)] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] [T2Space (ProbabilityMeasure Y)] [SecondCountableTopologyEither X Y]
  {l : Filter ι} {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y}
  {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} {cs : ι → X × Y → ℝ≥0∞}
  {c : X × Y → ℝ≥0∞}

/-- **The limiting optimal value is a lower bound.** Under the liminf hypothesis and tightness of
the two marginal families, the optimal value of the limiting problem is at most the `liminf` of the
optimal values of the moving problems.

The proof is by contradiction. If some `a` sits strictly between the two, then the moving problems
frequently admit a plan of cost below `a`; the compactness theorem turns those plans into a weakly
convergent refinement, and the liminf hypothesis bounds the limiting optimal value by `a`. No
optimal plan of any of the moving problems is needed — nearly optimal ones suffice, so no lower
semicontinuity of the moving costs is assumed. -/
theorem transportCost_le_liminf_transportCost (hcs : IsCostLiminfStable l cs μs νs c)
    (hμt : IsTightMeasureSet (Set.range fun i ↦ (μs i).toMeasure))
    (hνt : IsTightMeasureSet (Set.range fun i ↦ (νs i).toMeasure))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) :
    transportCost c μ.toMeasure ν.toMeasure ≤
      liminf (fun i ↦ transportCost (cs i) (μs i).toMeasure (νs i).toMeasure) l := by
  by_contra hcon
  obtain ⟨a, ha₁, ha₂⟩ := exists_between (not_le.mp hcon)
  -- Frequently along `l`, the moving problem has value below `a`.
  have hfreq : ∃ᶠ i in l, transportCost (cs i) (μs i).toMeasure (νs i).toMeasure < a := by
    intro hcon'
    have hev : ∀ᶠ i in l, a ≤ transportCost (cs i) (μs i).toMeasure (νs i).toMeasure := by
      simpa only [not_lt] using hcon'
    exact absurd (le_liminf_of_le (h := hev)) (not_le.mpr ha₁)
  -- Choose a plan of cost below `a` whenever there is one, and the product plan otherwise.
  have hchoice : ∀ i, ∃ σ : ProbabilityMeasure (X × Y),
      IsCoupling σ.toMeasure (μs i).toMeasure (νs i).toMeasure ∧
        (transportCost (cs i) (μs i).toMeasure (νs i).toMeasure < a →
          ∫⁻ z, cs i z ∂σ.toMeasure < a) := by
    intro i
    by_cases hi : transportCost (cs i) (μs i).toMeasure (νs i).toMeasure < a
    · obtain ⟨σ, hσ, hσa⟩ := transportCost_lt_iff.mp hi
      have : IsProbabilityMeasure (μs i).toMeasure := (μs i).2
      have : IsProbabilityMeasure σ := hσ.isProbabilityMeasure
      exact ⟨⟨σ, ‹_›⟩, hσ, fun _ ↦ hσa⟩
    · exact ⟨(Coupling.prod (μs i) (νs i)).1, (Coupling.prod (μs i) (νs i)).2, fun h ↦ absurd h hi⟩
  choose πs hπs hπsa using hchoice
  set lb : Filter ι :=
    l ⊓ 𝓟 {i | transportCost (cs i) (μs i).toMeasure (νs i).toMeasure < a}
  have hne : lb.NeBot := frequently_mem_iff_neBot.mp hfreq
  have := hne
  have hmem : ∀ᶠ i in lb, transportCost (cs i) (μs i).toMeasure (νs i).toMeasure < a :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hi ↦ hi)
  obtain ⟨l'', π, hne'', hle'', hconv, hπcoup⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    hμt hνt hμ hν (l' := lb) inf_le_left (Eventually.of_forall hπs)
  have := hne''
  have hbd : liminf (fun i ↦ ∫⁻ z, cs i z ∂(πs i).toMeasure) l'' ≤ a :=
    (liminf_le_liminf ((hmem.filter_mono hle'').mono fun i hi ↦ (hπsa i hi).le)).trans
      (le_of_eq (liminf_const a))
  have hfinal := (transportCost_le_lintegral hπcoup c).trans
    ((hcs.le_liminf hne'' (hle''.trans inf_le_left) (Eventually.of_forall hπs) hconv).trans hbd)
  exact absurd hfinal (not_le.mpr ha₂)

end Lower

section Upper

/-! The upper bound needs neither compactness nor a Hausdorff space of marginals. -/

variable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopologyEither X Y]
  {l : Filter ι} {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y}
  {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} {cs : ι → X × Y → ℝ≥0∞}
  {c : X × Y → ℝ≥0∞}

/-- **The limiting optimal value is an upper bound.** Under the recovery hypothesis, the `limsup` of
the optimal values of the moving problems is at most the optimal value of the limiting problem.
Neither compactness nor tightness is used: each coupling of the limiting marginals is tested
separately against its own recovery family. -/
theorem limsup_transportCost_le_transportCost (hrec : HasRecoveryPlans l cs μs νs c μ ν) :
    limsup (fun i ↦ transportCost (cs i) (μs i).toMeasure (νs i).toMeasure) l ≤
      transportCost c μ.toMeasure ν.toMeasure := by
  have : IsProbabilityMeasure μ.toMeasure := μ.2
  refine le_transportCost fun σ hσ ↦ ?_
  have : IsProbabilityMeasure σ := hσ.isProbabilityMeasure
  obtain ⟨πs, hπs, hlim⟩ := hrec.exists_recovery (π := ⟨σ, ‹_›⟩) hσ
  exact (limsup_le_limsup (hπs.mono fun i hi ↦ transportCost_le_lintegral hi _)).trans hlim

/-- **Fixed marginals admit recovery plans as soon as the costs do.** When the marginals are
eventually the limiting ones, a coupling of them is already feasible for every problem in the
family, so it recovers itself and only the asymptotic cost inequality is left to check. This is the
regime in which nothing but the cost moves, for instance `cs i = c + ε i • d` with `ε i → 0` and `d`
bounded. -/
theorem hasRecoveryPlans_of_limsup_le (hμs : ∀ᶠ i in l, μs i = μ) (hνs : ∀ᶠ i in l, νs i = ν)
    (hcs : ∀ π : ProbabilityMeasure (X × Y), IsCoupling π.toMeasure μ.toMeasure ν.toMeasure →
      limsup (fun i ↦ ∫⁻ z, cs i z ∂π.toMeasure) l ≤ ∫⁻ z, c z ∂π.toMeasure) :
    HasRecoveryPlans l cs μs νs c μ ν :=
  ⟨fun {π} hπ ↦ ⟨fun _ ↦ π, by filter_upwards [hμs, hνs] with i hi hi'; rw [hi, hi']; exact hπ,
    hcs π hπ⟩⟩

end Upper

section Stability

/-! Both bounds together. -/

variable {ι X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [T2Space (ProbabilityMeasure X)] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] [T2Space (ProbabilityMeasure Y)] [SecondCountableTopologyEither X Y]
  {l : Filter ι} {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y}
  {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} {cs : ι → X × Y → ℝ≥0∞}
  {c : X × Y → ℝ≥0∞}

/-- **Convergence of the optimal values.** With both stability hypotheses the optimal values of the
moving problems converge to the optimal value of the limiting problem, in `ℝ≥0∞`; no finiteness is
assumed anywhere, so the common value may be `∞`. -/
theorem tendsto_transportCost (hcs : IsCostLiminfStable l cs μs νs c)
    (hrec : HasRecoveryPlans l cs μs νs c μ ν)
    (hμt : IsTightMeasureSet (Set.range fun i ↦ (μs i).toMeasure))
    (hνt : IsTightMeasureSet (Set.range fun i ↦ (νs i).toMeasure))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) :
    Tendsto (fun i ↦ transportCost (cs i) (μs i).toMeasure (νs i).toMeasure) l
      (𝓝 (transportCost c μ.toMeasure ν.toMeasure)) :=
  tendsto_of_le_liminf_of_limsup_le (transportCost_le_liminf_transportCost hcs hμt hνt hμ hν)
    (limsup_transportCost_le_transportCost hrec)

omit [T2Space X] [T2Space Y] in
/-- **A weak limit of optimal plans is optimal.** If the plans `πs i` are eventually optimal for the
moving problems along a filter `l'` refining `l` and converge weakly to `π`, then `π` is an optimal
plan of the limiting problem. The liminf hypothesis bounds the cost of `π` by the asymptotic optimal
value along `l'`, and the recovery hypothesis bounds that in turn by the limiting optimal value. -/
theorem isOptimalCoupling_of_tendsto (hcs : IsCostLiminfStable l cs μs νs c)
    (hrec : HasRecoveryPlans l cs μs νs c μ ν) (hμ : Tendsto μs l (𝓝 μ))
    (hν : Tendsto νs l (𝓝 ν)) {l' : Filter ι} (hne : l'.NeBot) (hl' : l' ≤ l)
    {πs : ι → ProbabilityMeasure (X × Y)} {π : ProbabilityMeasure (X × Y)}
    (hopt : ∀ᶠ i in l',
      IsOptimalCoupling (cs i) (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure)
    (hπ : Tendsto πs l' (𝓝 π)) :
    IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure := by
  have := hne
  have hfeas : ∀ᶠ i in l', IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure :=
    hopt.mono fun i hi ↦ hi.toIsCoupling
  have hπcoup : IsCoupling π.toMeasure μ.toMeasure ν.toMeasure :=
    isCoupling_of_tendsto hl' hfeas hπ hμ hν
  have hcost : liminf (fun i ↦ ∫⁻ z, cs i z ∂(πs i).toMeasure) l' ≤
      limsup (fun i ↦ transportCost (cs i) (μs i).toMeasure (νs i).toMeasure) l := by
    rw [liminf_congr (hopt.mono fun i hi ↦ hi.lintegral_eq)]
    exact le_trans liminf_le_limsup (limsup_le_limsup_of_le hl')
  refine ⟨hπcoup, le_antisymm (((hcs.le_liminf hne hl' hfeas hπ).trans hcost).trans
    (limsup_transportCost_le_transportCost hrec)) (transportCost_le_lintegral hπcoup c)⟩

/-- **Subsequential convergence of optimal plans.** A family of optimal plans of the moving problems
always has a weakly convergent refinement, and every such limit is an optimal plan of the limiting
problem; in particular the limit is a cluster point of the family along `l`. This is the plan-level
counterpart of `TauCeti.tendsto_transportCost`. -/
theorem exists_isOptimalCoupling_tendsto [l.NeBot] (hcs : IsCostLiminfStable l cs μs νs c)
    (hrec : HasRecoveryPlans l cs μs νs c μ ν)
    (hμt : IsTightMeasureSet (Set.range fun i ↦ (μs i).toMeasure))
    (hνt : IsTightMeasureSet (Set.range fun i ↦ (νs i).toMeasure))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    {πs : ι → ProbabilityMeasure (X × Y)}
    (hopt : ∀ᶠ i in l,
      IsOptimalCoupling (cs i) (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure) :
    ∃ (l' : Filter ι) (π : ProbabilityMeasure (X × Y)), l'.NeBot ∧ l' ≤ l ∧
      Tendsto πs l' (𝓝 π) ∧ MapClusterPt π l πs ∧
        IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure := by
  obtain ⟨l', π, hne, hle, hconv, -⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet hμt hνt
    hμ hν (l' := l) le_rfl (hopt.mono fun i hi ↦ hi.toIsCoupling)
  have := hne
  exact ⟨l', π, hne, hle, hconv, hconv.mapClusterPt.mono hle,
    isOptimalCoupling_of_tendsto hcs hrec hμ hν hne hle (hopt.filter_mono hle) hconv⟩

end Stability

section Polish

/-! The Polish specialisation. On a Polish space a weakly convergent *sequence* of probability
measures is tight, by the converse half of Prokhorov's theorem applied to the compact set formed by
the sequence and its limit; so the tightness hypotheses of the previous section are automatic there
and the statements below carry none. -/

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {μs : ℕ → ProbabilityMeasure X} {νs : ℕ → ProbabilityMeasure Y} {μ : ProbabilityMeasure X}
  {ν : ProbabilityMeasure Y} {cs : ℕ → X × Y → ℝ≥0∞} {c : X × Y → ℝ≥0∞}

/-- **A weakly convergent sequence of probability measures on a Polish space is tight.** The
sequence together with its limit is a compact, hence closed, set of probability measures, and the
converse half of Prokhorov's theorem turns compactness back into tightness. -/
theorem isTightMeasureSet_range_of_tendsto (hμ : Tendsto μs atTop (𝓝 μ)) :
    IsTightMeasureSet (Set.range fun n ↦ (μs n).toMeasure) := by
  -- Prokhorov's converse asks for a complete metric; a Polish topology supplies one.
  let : MetricSpace X := TopologicalSpace.completelyMetrizableMetric X
  have : CompleteSpace X := TopologicalSpace.complete_completelyMetrizableMetric X
  have hcompact : IsCompact (insert μ (Set.range μs)) := hμ.isCompact_insert_range
  refine (MeasureTheory.isTightMeasureSet_of_isCompact_closure
    (S := insert μ (Set.range μs)) (by rwa [hcompact.isClosed.closure_eq])).subset ?_
  rintro - ⟨n, rfl⟩
  exact ⟨μs n, Or.inr (mem_range_self n), rfl⟩

/-- **Convergence of the optimal values on Polish spaces**, with no tightness hypothesis: weak
convergence of the two marginal sequences supplies it. -/
theorem tendsto_transportCost_of_polishSpace (hcs : IsCostLiminfStable atTop cs μs νs c)
    (hrec : HasRecoveryPlans atTop cs μs νs c μ ν) (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : Tendsto νs atTop (𝓝 ν)) :
    Tendsto (fun n ↦ transportCost (cs n) (μs n).toMeasure (νs n).toMeasure) atTop
      (𝓝 (transportCost c μ.toMeasure ν.toMeasure)) :=
  tendsto_transportCost hcs hrec (isTightMeasureSet_range_of_tendsto hμ)
    (isTightMeasureSet_range_of_tendsto hν) hμ hν

/-- **Subsequential convergence of optimal plans on Polish spaces**, with no tightness
hypothesis. -/
theorem exists_isOptimalCoupling_tendsto_of_polishSpace (hcs : IsCostLiminfStable atTop cs μs νs c)
    (hrec : HasRecoveryPlans atTop cs μs νs c μ ν) (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : Tendsto νs atTop (𝓝 ν)) {πs : ℕ → ProbabilityMeasure (X × Y)}
    (hopt : ∀ᶠ n in atTop,
      IsOptimalCoupling (cs n) (πs n).toMeasure (μs n).toMeasure (νs n).toMeasure) :
    ∃ (l : Filter ℕ) (π : ProbabilityMeasure (X × Y)), l.NeBot ∧ l ≤ atTop ∧
      Tendsto πs l (𝓝 π) ∧ MapClusterPt π atTop πs ∧
        IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure :=
  exists_isOptimalCoupling_tendsto hcs hrec (isTightMeasureSet_range_of_tendsto hμ)
    (isTightMeasureSet_range_of_tendsto hν) hμ hν hopt

/-- **The optimal transport cost of a lower semicontinuous cost is weakly lower semicontinuous in
the marginals.** This is the fixed-cost corollary: the liminf hypothesis is automatic, so no
stability assumption survives. The reverse inequality genuinely fails without a recovery hypothesis
— the optimal value can drop in the limit — which is why only one bound is stated here. -/
theorem transportCost_le_liminf_transportCost_of_lowerSemicontinuous (hc : LowerSemicontinuous c)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν)) :
    transportCost c μ.toMeasure ν.toMeasure ≤
      liminf (fun n ↦ transportCost c (μs n).toMeasure (νs n).toMeasure) atTop :=
  transportCost_le_liminf_transportCost
    (isCostLiminfStable_const (μs := μs) (νs := νs) hc)
    (isTightMeasureSet_range_of_tendsto hμ) (isTightMeasureSet_range_of_tendsto hν) hμ hν

/-- **Stability for a family of costs above a lower semicontinuous limit, with fixed marginals.**
Both hypotheses are discharged here: liminf-stability from lower semicontinuity of the limiting
cost, and recovery from the asymptotic cost inequality on each coupling. A cost family such as
`cs n = c + d / n` with `d` bounded satisfies both, so the statement is not vacuous. -/
theorem tendsto_transportCost_of_const_marginals (hc : LowerSemicontinuous c)
    (hle : ∀ᶠ n in atTop, c ≤ cs n)
    (hlim : ∀ π : ProbabilityMeasure (X × Y), IsCoupling π.toMeasure μ.toMeasure ν.toMeasure →
      limsup (fun n ↦ ∫⁻ z, cs n z ∂π.toMeasure) atTop ≤ ∫⁻ z, c z ∂π.toMeasure) :
    Tendsto (fun n ↦ transportCost (cs n) μ.toMeasure ν.toMeasure) atTop
      (𝓝 (transportCost c μ.toMeasure ν.toMeasure)) :=
  tendsto_transportCost_of_polishSpace (μs := fun _ ↦ μ) (νs := fun _ ↦ ν)
    (isCostLiminfStable_of_le hc hle)
    (hasRecoveryPlans_of_limsup_le (Eventually.of_forall fun _ ↦ rfl)
      (Eventually.of_forall fun _ ↦ rfl) hlim)
    tendsto_const_nhds tendsto_const_nhds

end Polish

end TauCeti
