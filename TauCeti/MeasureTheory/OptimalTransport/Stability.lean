/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
public import TauCeti.MeasureTheory.Measure.Prokhorov
public import TauCeti.MeasureTheory.OptimalTransport.Compactness
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic
-- Proof-only: the order-topology criterion turning a `liminf`/`limsup` sandwich into convergence.
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
every moving problem then has value `1`, while the limiting problem has value `0`. The recovery
family must converge weakly to the chosen limiting plan as well as satisfy the cost bound; this is
the recovery-coupling condition from the roadmap.

The two bounds are separated on purpose: `TauCeti.transportCost_le_liminf_transportCost` needs the
liminf hypothesis and compactness, `TauCeti.limsup_transportCost_le_transportCost` needs the
recovery hypothesis and nothing else, and only `TauCeti.tendsto_transportCost` needs both.

Compactness enters through `TauCeti.exists_isCoupling_tendsto_of_isTightMeasureSet`, proved in
`TauCeti.MeasureTheory.OptimalTransport.Compactness`: a family of plans whose (varying) marginals
are tight on a filter tail is relatively compact, and every weak limit along a finer filter is a
coupling of the limiting marginals. This is the "tightness of optimizer subsequences" step, and it
is what lets the arguments run along a filter rather than a sequence: passing to a subsequence is
replaced by passing to a finer filter.

## Main statements

* `TauCeti.IsCostLiminfStable` and `TauCeti.HasRecoveryPlans` — the two stability hypotheses, with
  `TauCeti.isCostLiminfStable_of_le` and `TauCeti.isCostLiminfStable_const` supplying the first one
  from lower semicontinuity;
* `TauCeti.transportCost_le_liminf_transportCost` and
  `TauCeti.limsup_transportCost_le_transportCost` — the two one-sided bounds on the optimal values;
* `TauCeti.hasRecoveryPlans_of_limsup_le` — the recovery hypothesis for a family with fixed
  marginals;
* `TauCeti.tendsto_transportCost` — convergence of the optimal values, with
  `TauCeti.tendsto_transportCost_of_const_marginals` as a topology-free fixed-marginal criterion;
* `TauCeti.isOptimalCoupling_of_tendsto` and `TauCeti.exists_isOptimalCoupling_tendsto` —
  subsequential convergence of optimal plans to an optimal plan of the limiting problem;
* `TauCeti.tendsto_transportCost_of_polishSpace` and
  `TauCeti.exists_isOptimalCoupling_tendsto_of_polishSpace` — the Polish sequential forms, where
  weak convergence supplies tightness and the stability theorems need no tightness hypothesis;
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

section Hypotheses

/-! The two stability hypotheses. Both are recorded as one-field structures so that they can be
consumed by name and produced by `refine ⟨fun ... ↦ ?_⟩`. -/

/-- The asymptotic lower bound half of stability: along every filter `l'` refining `l`, a weakly
convergent family of plans that is eventually feasible for the moving marginals `μs`, `νs` costs at
least the limiting cost `c` of its limit, asymptotically. Quantifying over the refinements of `l`
is what makes the hypothesis usable after passing to a convergent subfamily, exactly as the
classical statement quantifies over subsequences. -/
structure IsCostLiminfStable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace (X × Y)]
    (l : Filter ι) (cs : ι → X × Y → ℝ≥0∞)
    (μs : ι → ProbabilityMeasure X) (νs : ι → ProbabilityMeasure Y) (c : X × Y → ℝ≥0∞) :
    Prop where
  /-- The cost of a weak limit of feasible plans is at most the asymptotic cost of the family. -/
  le_liminf {l' : Filter ι} (hne : l'.NeBot) (hle : l' ≤ l)
    {πs : ι → ProbabilityMeasure (X × Y)} {π : ProbabilityMeasure (X × Y)}
    (hπs : ∀ᶠ i in l', IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure)
    (hπ : Tendsto πs l' (𝓝 π)) :
    ∫⁻ z, c z ∂π.toMeasure ≤ liminf (fun i ↦ ∫⁻ z, cs i z ∂(πs i).toMeasure) l'

/-- The asymptotic upper bound half of stability: every plan of the limiting problem is recovered
by a weakly convergent family of plans that is eventually feasible for the moving marginals and
costs no more asymptotically. -/
structure HasRecoveryPlans {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace (X × Y)]
    (l : Filter ι) (cs : ι → X × Y → ℝ≥0∞)
    (μs : ι → ProbabilityMeasure X) (νs : ι → ProbabilityMeasure Y) (c : X × Y → ℝ≥0∞)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) : Prop where
  /-- Every coupling of the limiting marginals is recovered weakly and from above in cost. -/
  exists_recovery {π : ProbabilityMeasure (X × Y)}
    (hπ : IsCoupling π.toMeasure μ.toMeasure ν.toMeasure) :
    ∃ πs : ι → ProbabilityMeasure (X × Y),
      (∀ᶠ i in l, IsCoupling (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure) ∧
        Tendsto πs l (𝓝 π) ∧
        limsup (fun i ↦ ∫⁻ z, cs i z ∂(πs i).toMeasure) l ≤ ∫⁻ z, c z ∂π.toMeasure

variable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace (X × Y)]
  {cs : ι → X × Y → ℝ≥0∞} {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y}
  {c : X × Y → ℝ≥0∞} {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}

/-- Liminf stability is preserved when the indexing filter is refined. -/
theorem IsCostLiminfStable.mono {l l' : Filter ι} (hcs : IsCostLiminfStable l cs μs νs c)
    (hle : l' ≤ l) : IsCostLiminfStable l' cs μs νs c :=
  ⟨fun hne hle' ↦ hcs.le_liminf hne (hle'.trans hle)⟩

/-- Recovery plans remain recovery plans when the indexing filter is refined. -/
theorem HasRecoveryPlans.mono {l l' : Filter ι} (hrec : HasRecoveryPlans l cs μs νs c μ ν)
    (hle : l' ≤ l) : HasRecoveryPlans l' cs μs νs c μ ν :=
  ⟨fun hπ ↦ by
    obtain ⟨πs, hfeas, hconv, hcost⟩ := hrec.exists_recovery hπ
    exact ⟨πs, hfeas.filter_mono hle, hconv.mono_left hle,
      (limsup_le_limsup_of_le hle).trans hcost⟩⟩

end Hypotheses

section LowerSemicontinuous

/-! Lower semicontinuity of the limiting cost, together with domination by the family, is the
standard source of `TauCeti.IsCostLiminfStable`. Only a compatible pseudometric and measurable
opens on the product are needed for the weak-topology lower semicontinuity of
`TauCeti.lowerSemicontinuous_lintegral_probabilityMeasure`. -/

variable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace (X × Y)]
  [TopologicalSpace.PseudoMetrizableSpace (X × Y)] {l : Filter ι}
  {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y} {cs : ι → X × Y → ℝ≥0∞}
  {c : X × Y → ℝ≥0∞}

/-- **A lower semicontinuous cost dominated by the family is liminf-stable.** Weak lower
semicontinuity of `π ↦ ∫⁻ c ∂π` gives the inequality for the limiting cost itself, and eventual
domination `c ≤ cs i` upgrades it to the moving costs. The feasibility of the plans plays no role:
the bound holds for every weakly convergent family. -/
theorem isCostLiminfStable_of_le (hc : LowerSemicontinuous c) (hcs : ∀ᶠ i in l, c ≤ cs i) :
    IsCostLiminfStable l cs μs νs c := by
  -- The lower semicontinuity theorem is phrased for a chosen compatible pseudometric.
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

section Lower

/-! The lower bound on the optimal values: it is the half that consumes compactness. -/

variable {ι X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [T2Space (ProbabilityMeasure X)] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] [T2Space (ProbabilityMeasure Y)] [SecondCountableTopologyEither X Y]
  {l : Filter ι} {μs : ι → ProbabilityMeasure X} {νs : ι → ProbabilityMeasure Y}
  {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} {cs : ι → X × Y → ℝ≥0∞}
  {c : X × Y → ℝ≥0∞}

/-- **The limiting optimal value is a lower bound.** Under the liminf hypothesis and tail tightness
of the two marginal families, the optimal value of the limiting problem is at most the `liminf` of
the optimal values of the moving problems. Nearly optimal plans suffice, so no lower
semicontinuity of the moving costs is assumed. -/
theorem transportCost_le_liminf_transportCost (hcs : IsCostLiminfStable l cs μs νs c)
    (hμt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (μs i).toMeasure) '' s))
    (hνt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (νs i).toMeasure) '' s))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) :
    transportCost c μ.toMeasure ν.toMeasure ≤
      liminf (fun i ↦ transportCost (cs i) (μs i).toMeasure (νs i).toMeasure) l := by
  by_contra hcon
  obtain ⟨a, ha₁, ha₂⟩ := exists_between (not_le.mp hcon)
  -- Frequently along `l`, the moving problem has value below `a`.
  have hfreq : ∃ᶠ i in l, transportCost (cs i) (μs i).toMeasure (νs i).toMeasure < a :=
    frequently_lt_of_liminf_lt (h := ha₁)
  -- Choose a plan of cost below `a` whenever there is one, and the product plan otherwise.
  have hchoice : ∀ i, ∃ σ : ProbabilityMeasure (X × Y),
      IsCoupling σ.toMeasure (μs i).toMeasure (νs i).toMeasure ∧
        (transportCost (cs i) (μs i).toMeasure (νs i).toMeasure < a →
          ∫⁻ z, cs i z ∂σ.toMeasure < a) := by
    intro i
    by_cases hi : transportCost (cs i) (μs i).toMeasure (νs i).toMeasure < a
    · obtain ⟨σ, hσ, hσa⟩ := transportCost_lt_iff.mp hi
      exact ⟨⟨σ, hσ.isProbabilityMeasure⟩, hσ, fun _ ↦ hσa⟩
    · exact ⟨(Coupling.prod (μs i) (νs i)).1, (Coupling.prod (μs i) (νs i)).2, fun h ↦ absurd h hi⟩
  choose πs hπs hπsa using hchoice
  set lb : Filter ι :=
    l ⊓ 𝓟 {i | transportCost (cs i) (μs i).toMeasure (νs i).toMeasure < a}
  have hne : lb.NeBot := frequently_mem_iff_neBot.mp hfreq
  have := hne
  have hmem : ∀ᶠ i in lb, transportCost (cs i) (μs i).toMeasure (νs i).toMeasure < a :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hi ↦ hi)
  obtain ⟨s, hs, hμs⟩ := hμt
  obtain ⟨t, ht, hνt⟩ := hνt
  obtain ⟨l'', π, hne'', hle'', hconv, hπcoup⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet
    (l := lb) ⟨s, mem_inf_of_left hs, hμs⟩ ⟨t, mem_inf_of_left ht, hνt⟩
    (hμ.mono_left inf_le_left) (hν.mono_left inf_le_left) (Eventually.of_forall hπs)
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

variable {ι X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace (X × Y)]
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
  refine le_transportCost fun σ hσ ↦ ?_
  obtain ⟨πs, hπs, -, hlim⟩ :=
    hrec.exists_recovery (π := ⟨σ, hσ.isProbabilityMeasure⟩) hσ
  exact (limsup_le_limsup (hπs.mono fun i hi ↦ transportCost_le_lintegral hi _)).trans hlim

/-- **Fixed marginals admit recovery plans as soon as the costs do.** When the marginals are
eventually the limiting ones, a coupling of them is eventually feasible for the moving problems,
so it recovers itself and only the asymptotic cost inequality is left to check. This is the
regime in which nothing but the cost moves, for instance `cs i = c + ε i • d` with `ε i → 0` and `d`
bounded. -/
theorem hasRecoveryPlans_of_limsup_le (hμs : ∀ᶠ i in l, μs i = μ) (hνs : ∀ᶠ i in l, νs i = ν)
    (hcs : ∀ π : ProbabilityMeasure (X × Y), IsCoupling π.toMeasure μ.toMeasure ν.toMeasure →
      limsup (fun i ↦ ∫⁻ z, cs i z ∂π.toMeasure) l ≤ ∫⁻ z, c z ∂π.toMeasure) :
    HasRecoveryPlans l cs μs νs c μ ν :=
  ⟨fun {π} hπ ↦ ⟨fun _ ↦ π, by filter_upwards [hμs, hνs] with i hi hi'; rw [hi, hi']; exact hπ,
    tendsto_const_nhds, hcs π hπ⟩⟩

end Upper

section FixedMarginals

variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {l : Filter ι}
  {cs : ι → X × Y → ℝ≥0∞} {c : X × Y → ℝ≥0∞} {μ : Measure X} {ν : Measure Y}

/-- **Convergence of transport costs with fixed marginals.** If the moving costs eventually
dominate the limiting cost, this supplies the `liminf` bound by monotonicity. A pointwise `limsup`
bound on the integral along every coupling supplies the reverse bound. No topology, tightness, or
lower semicontinuity is needed. -/
theorem tendsto_transportCost_of_const_marginals (hle : ∀ᶠ i in l, c ≤ cs i)
    (hlim : ∀ π, IsCoupling π μ ν →
      limsup (fun i ↦ ∫⁻ z, cs i z ∂π) l ≤ ∫⁻ z, c z ∂π) :
    Tendsto (fun i ↦ transportCost (cs i) μ ν) l (𝓝 (transportCost c μ ν)) := by
  refine tendsto_of_le_liminf_of_limsup_le
    (le_liminf_of_le (by isBoundedDefault) (hle.mono fun _ hi ↦ transportCost_mono hi)) ?_
  exact le_transportCost fun π hπ ↦
    (limsup_le_limsup (Eventually.of_forall fun i ↦ transportCost_le_lintegral hπ _)).trans
      (hlim π hπ)

end FixedMarginals

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
    (hμt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (μs i).toMeasure) '' s))
    (hνt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (νs i).toMeasure) '' s))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν)) :
    Tendsto (fun i ↦ transportCost (cs i) (μs i).toMeasure (νs i).toMeasure) l
      (𝓝 (transportCost c μ.toMeasure ν.toMeasure)) :=
  tendsto_of_le_liminf_of_limsup_le (transportCost_le_liminf_transportCost hcs hμt hνt hμ hν)
    (limsup_transportCost_le_transportCost hrec)

omit [T2Space X] [T2Space Y] in
/-- **A weak limit of optimal plans is optimal.** If the plans `πs i` are eventually optimal for the
moving problems along a filter `l'` refining `l` and converge weakly to `π`, then `π` is an optimal
plan of the limiting problem, provided the moving optimal values have the required `limsup` upper
bound. -/
theorem isOptimalCoupling_of_tendsto (hcs : IsCostLiminfStable l cs μs νs c)
    (hval : limsup (fun i ↦ transportCost (cs i) (μs i).toMeasure (νs i).toMeasure) l ≤
      transportCost c μ.toMeasure ν.toMeasure) (hμ : Tendsto μs l (𝓝 μ))
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
    isCoupling_of_tendsto hfeas hπ (hμ.mono_left hl') (hν.mono_left hl')
  have hcost : liminf (fun i ↦ ∫⁻ z, cs i z ∂(πs i).toMeasure) l' ≤
      limsup (fun i ↦ transportCost (cs i) (μs i).toMeasure (νs i).toMeasure) l := by
    rw [liminf_congr (hopt.mono fun i hi ↦ hi.lintegral_eq)]
    exact le_trans liminf_le_limsup (limsup_le_limsup_of_le hl')
  refine ⟨hπcoup, le_antisymm (((hcs.le_liminf hne hl' hfeas hπ).trans hcost).trans
    hval) (transportCost_le_lintegral hπcoup c)⟩

/-- **Subsequential convergence of optimal plans.** A family of optimal plans of the moving problems
has a refinement along which the plans converge to an optimal plan of the limiting problem. The
theorem `TauCeti.isOptimalCoupling_of_tendsto` says that every such weak limit is optimal under the
explicit `limsup` upper bound on the moving optimal values. -/
theorem exists_isOptimalCoupling_tendsto [l.NeBot] (hcs : IsCostLiminfStable l cs μs νs c)
    (hval : limsup (fun i ↦ transportCost (cs i) (μs i).toMeasure (νs i).toMeasure) l ≤
      transportCost c μ.toMeasure ν.toMeasure)
    (hμt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (μs i).toMeasure) '' s))
    (hνt : ∃ s ∈ l, IsTightMeasureSet ((fun i ↦ (νs i).toMeasure) '' s))
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    {πs : ι → ProbabilityMeasure (X × Y)}
    (hopt : ∀ᶠ i in l,
      IsOptimalCoupling (cs i) (πs i).toMeasure (μs i).toMeasure (νs i).toMeasure) :
    ∃ (l' : Filter ι) (π : ProbabilityMeasure (X × Y)), l'.NeBot ∧ l' ≤ l ∧
      Tendsto πs l' (𝓝 π) ∧ MapClusterPt π l πs ∧
        IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure := by
  obtain ⟨l', π, hne, hle, hconv, -⟩ := exists_isCoupling_tendsto_of_isTightMeasureSet hμt hνt
    hμ hν (hopt.mono fun i hi ↦ hi.toIsCoupling)
  have := hne
  exact ⟨l', π, hne, hle, hconv, hconv.mapClusterPt.mono hle,
    isOptimalCoupling_of_tendsto hcs hval hμ hν hne hle (hopt.filter_mono hle) hconv⟩

end Stability

private theorem exists_isTightMeasureSet_image {ι X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {l : Filter ι} {f : ι → Measure X} {S : Set (Measure X)}
    (hS : IsTightMeasureSet S) (hf : ∀ i, f i ∈ S) :
    ∃ s ∈ l, IsTightMeasureSet (f '' s) :=
  ⟨univ, univ_mem, hS.subset (by rintro - ⟨i, -, rfl⟩; exact hf i)⟩

section Polish

/-! The Polish specialisation. On a Polish space a weakly convergent *sequence* of probability
measures is tight, by the converse half of Prokhorov's theorem applied to the compact set formed by
the sequence and its limit; so the tightness hypotheses of the previous section are automatic there
and the statements below carry none. -/

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {μs : ℕ → ProbabilityMeasure X} {νs : ℕ → ProbabilityMeasure Y} {μ : ProbabilityMeasure X}
  {ν : ProbabilityMeasure Y} {cs : ℕ → X × Y → ℝ≥0∞} {c : X × Y → ℝ≥0∞}

/-- **Convergence of the optimal values on Polish spaces**, with no tightness hypothesis: weak
convergence of the two marginal sequences supplies it. -/
theorem tendsto_transportCost_of_polishSpace (hcs : IsCostLiminfStable atTop cs μs νs c)
    (hrec : HasRecoveryPlans atTop cs μs νs c μ ν) (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : Tendsto νs atTop (𝓝 ν)) :
    Tendsto (fun n ↦ transportCost (cs n) (μs n).toMeasure (νs n).toMeasure) atTop
      (𝓝 (transportCost c μ.toMeasure ν.toMeasure)) :=
  tendsto_transportCost hcs hrec
    (exists_isTightMeasureSet_image (isTightMeasureSet_range_of_tendsto hμ) mem_range_self)
    (exists_isTightMeasureSet_image (isTightMeasureSet_range_of_tendsto hν) mem_range_self) hμ hν

/-- **Subsequential convergence of optimal plans on Polish spaces**, with no tightness hypothesis.
The `limsup` upper bound on the moving optimal values is still assumed explicitly. -/
theorem exists_isOptimalCoupling_tendsto_of_polishSpace (hcs : IsCostLiminfStable atTop cs μs νs c)
    (hval : limsup (fun n ↦ transportCost (cs n) (μs n).toMeasure (νs n).toMeasure) atTop ≤
      transportCost c μ.toMeasure ν.toMeasure) (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : Tendsto νs atTop (𝓝 ν)) {πs : ℕ → ProbabilityMeasure (X × Y)}
    (hopt : ∀ᶠ n in atTop,
      IsOptimalCoupling (cs n) (πs n).toMeasure (μs n).toMeasure (νs n).toMeasure) :
    ∃ (π : ProbabilityMeasure (X × Y)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (πs ∘ φ) atTop (𝓝 π) ∧
        IsOptimalCoupling c π.toMeasure μ.toMeasure ν.toMeasure := by
  obtain ⟨-, π, -, -, -, hcluster, hπ⟩ := exists_isOptimalCoupling_tendsto hcs hval
    (exists_isTightMeasureSet_image (isTightMeasureSet_range_of_tendsto hμ) mem_range_self)
    (exists_isTightMeasureSet_image (isTightMeasureSet_range_of_tendsto hν) mem_range_self)
    hμ hν hopt
  obtain ⟨φ, hφ, hconv⟩ := hcluster.tendsto_subseq
  exact ⟨π, φ, hφ, hconv, hπ⟩

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
    (exists_isTightMeasureSet_image (isTightMeasureSet_range_of_tendsto hμ) mem_range_self)
    (exists_isTightMeasureSet_image (isTightMeasureSet_range_of_tendsto hν) mem_range_self) hμ hν

end Polish

end TauCeti
