/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.MeasureTheory.OptimalTransport.Cost

/-!
# Transport maps and their graph plans

A *transport map* from `μ` to `ν` is a map `T : X → Y` whose law under `μ` is `ν`, that is, one
with `μ.map T = ν`. This is Mathlib's `ProbabilityTheory.HasLaw T ν μ`, and nothing in this file
redefines it: the optimal-transport side of the story is not the predicate but the *graph plan*
`TauCeti.graphPlan μ T`, the pushforward of `μ` along `x ↦ (x, T x)`, which turns a transport map
into a transport plan and so embeds the Monge problem into the Kantorovich problem.

The embedding is not surjective, and the failure is already visible on a one-point source: a
transport map out of a Dirac measure cannot split mass, so its target is again a Dirac measure
(`TauCeti.eq_dirac_of_hasLaw_dirac`), while `δ_x` has a coupling with *every* probability measure
`ν`. Conversely a plan concentrated on the graph of an almost everywhere measurable map is that
map's graph plan (`TauCeti.IsCoupling.eq_graphPlan_of_ae`), so the graph plans are exactly the
deterministic plans.

The raw-measure API is stated for arbitrary measures on arbitrary measurable spaces; no topology,
metric, density or normalisation is involved, and the source and target spaces may differ. Only
the final bundled coupling construction requires probability measures.

## Main definitions

* `TauCeti.graphPlan μ T` — the graph plan, or deterministic transport plan, of `T` under `μ`:
  the pushforward of `μ` along `x ↦ (x, T x)`;
* `TauCeti.Coupling.graphPlan` — the same construction as a bundled coupling of two probability
  measures, given a transport map between them.

## Main statements

* `TauCeti.fst_graphPlan` and `TauCeti.snd_graphPlan` — the two marginals of a graph plan, and
  with them `TauCeti.isCoupling_graphPlan` and `TauCeti.isCoupling_graphPlan_of_hasLaw`: a
  transport map from `μ` to `ν` induces a coupling of `μ` and `ν`;
* `TauCeti.transportCost_le_lintegral_of_hasLaw` — **the Monge problem dominates the Kantorovich
  problem**: the transport cost of `μ` and `ν` is at most the cost `∫⁻ x, c (x, T x) ∂μ` of any
  transport map `T` from `μ` to `ν`;
* `TauCeti.IsCoupling.eq_graphPlan_of_ae` — a plan carried by the graph of an almost everywhere
  measurable map is that map's graph plan, the converse of `TauCeti.isCoupling_graphPlan`;
* `TauCeti.graphPlan_dirac` and `TauCeti.eq_dirac_of_hasLaw_dirac` — a Dirac source admits only
  Dirac targets, so the Monge problem out of an atom is infeasible whenever the Kantorovich
  problem is not;
* `TauCeti.map_prodMap_id_graphPlan` — the composite of two maps has the graph plan obtained by
  pushing the first map's graph plan forward in its second coordinate.

## Implementation notes

Feasibility of a transport map is `ProbabilityTheory.HasLaw T ν μ` throughout; this file adds no
predicate of its own, so the Mathlib API for laws — `ProbabilityTheory.HasLaw.comp`,
`ProbabilityTheory.HasLaw.congr`, `ProbabilityTheory.HasLaw.id` and
`MeasureTheory.MeasurePreserving.hasLaw` — applies to transport maps verbatim. In particular,
these feed directly into `TauCeti.isCoupling_graphPlan_of_hasLaw` without intermediate wrappers.

`ProbabilityTheory.HasLaw` asks only for almost-everywhere measurability, so that is the running
hypothesis here too. It is genuinely needed for the *first* marginal: `MeasureTheory.Measure.map`
is `0` on a non-almost-everywhere-measurable map, so `TauCeti.fst_graphPlan` fails without it. The
second marginal (`TauCeti.snd_graphPlan`) needs no hypothesis, because in that degenerate case both
sides are `0`.

`TauCeti.graphPlan_def` is the stable rewriting interface to the pushforward implementation.

This is Layer 0, item 2 of the optimal-transport roadmap.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003, §1.1,
  where Monge's problem asks for a map `T` pushing `μ` forward to `ν` and the transference plan it
  induces is `(id × T)_# μ`. Villani takes Borel maps and probability measures;
  `TauCeti.graphPlan` is defined for an arbitrary map and an arbitrary measure, and is a coupling
  exactly when the map is a transport map.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, 2009, Chapter 1, where couplings
  of this form are called *deterministic*.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} {σ : Measure Z} {π : Measure (X × Y)}
  {T : X → Y} {S : Y → Z} {c : X × Y → ℝ≥0∞} {x : X}

/-- The graph plan, or deterministic transport plan, of a map `T : X → Y` under a measure `μ` on
`X`: the pushforward of `μ` along `x ↦ (x, T x)`. It is a coupling of `μ` and `μ.map T` as soon as
`T` is almost everywhere measurable (`TauCeti.isCoupling_graphPlan`), and this is how a solution of
the Monge problem is read as a solution of the Kantorovich problem. -/
def graphPlan (μ : Measure X) (T : X → Y) : Measure (X × Y) :=
  μ.map fun x ↦ (x, T x)

/-- The graph plan is the pushforward of the source measure along the graph map. -/
theorem graphPlan_def (μ : Measure X) (T : X → Y) :
    graphPlan μ T = μ.map fun x ↦ (x, T x) :=
  (rfl)

/-- The mass a graph plan gives a measurable set is the source mass of its preimage under the
graph map. -/
theorem graphPlan_apply (hT : AEMeasurable T μ) {s : Set (X × Y)} (hs : MeasurableSet s) :
    graphPlan μ T s = μ {x | (x, T x) ∈ s} :=
  Measure.map_apply_of_aemeasurable (measurable_id'.aemeasurable.prodMk hT) hs

/-- The first marginal of a graph plan is the source measure. This needs `T` to be almost
everywhere measurable: otherwise the pushforward defining the plan is `0`. -/
theorem fst_graphPlan (hT : AEMeasurable T μ) : (graphPlan μ T).fst = μ :=
  (Measure.fst_map_prodMk₀ hT).trans Measure.map_id'

/-- The second marginal of a graph plan is the law of the map. No measurability is needed: if `T`
is not almost everywhere measurable then both sides are `0`. -/
@[simp]
theorem snd_graphPlan (μ : Measure X) (T : X → Y) : (graphPlan μ T).snd = μ.map T :=
  Measure.snd_map_prodMk₀ measurable_id'.aemeasurable

/-- Almost everywhere equal maps have the same graph plan. Together with
`ProbabilityTheory.HasLaw.congr`, which transports feasibility along the same relation, this says
that the Monge problem only sees a transport map through its class modulo `μ`-null sets. -/
theorem graphPlan_congr {T' : X → Y} (h : T =ᵐ[μ] T') : graphPlan μ T = graphPlan μ T' :=
  Measure.map_congr <| by filter_upwards [h] with x hx; rw [hx]

/-- The graph plan of an almost everywhere measurable map is a coupling of the source measure and
the law of the map. -/
theorem isCoupling_graphPlan (hT : AEMeasurable T μ) :
    IsCoupling (graphPlan μ T) μ (μ.map T) :=
  ⟨fst_graphPlan hT, snd_graphPlan μ T⟩

/-- **A transport map induces a transport plan**: the graph plan of a map with law `ν` under `μ`
is a coupling of `μ` and `ν`. -/
theorem isCoupling_graphPlan_of_hasLaw (hT : HasLaw T ν μ) : IsCoupling (graphPlan μ T) μ ν :=
  ⟨fst_graphPlan hT.aemeasurable, (snd_graphPlan μ T).trans hT.map_eq⟩

/-- The graph plan of a transport map between probability measures is a probability measure. -/
theorem isProbabilityMeasure_graphPlan [IsProbabilityMeasure μ] (hT : AEMeasurable T μ) :
    IsProbabilityMeasure (graphPlan μ T) :=
  (isCoupling_graphPlan hT).isProbabilityMeasure

/-- The generic graph-plan interface specializes directly to the identity map. -/
example (μ : Measure X) : IsCoupling (graphPlan μ (id : X → X)) μ μ :=
  isCoupling_graphPlan_of_hasLaw HasLaw.id

/-- The generic graph-plan interface also specializes directly to a measurable equivalence. -/
example (μ : Measure X) (e : X ≃ᵐ Y) :
    IsCoupling (graphPlan μ e) μ (μ.map e) :=
  isCoupling_graphPlan e.measurable.aemeasurable

/-- The graph plan of a measurable equivalence and the graph plan of its inverse are exchanged by
the coordinate swap: a bijective transport map transports in both directions, and reversing it
reverses the plan. -/
theorem map_swap_graphPlan_symm (μ : Measure X) (e : X ≃ᵐ Y) :
    (graphPlan (μ.map e) e.symm).map Prod.swap = graphPlan μ e := by
  have h : graphPlan (μ.map e) e.symm = μ.map fun x ↦ (e x, x) := by
    rw [graphPlan, Measure.map_map (measurable_id'.prodMk e.symm.measurable) e.measurable]
    exact Measure.map_congr (Filter.Eventually.of_forall fun x ↦ by simp)
  rw [h, Measure.map_map measurable_swap (e.measurable.prodMk measurable_id')]
  rfl

/-! ### Graph plans over a Dirac source -/

private theorem map_dirac_of_aemeasurable (hT : AEMeasurable T (Measure.dirac x)) :
    (Measure.dirac x).map T = Measure.dirac (T x) := by
  have hx : T x = hT.mk T x := by
    by_contra hx
    have hmem : x ∈ {y | T y = hT.mk T y}ᶜ := by simpa
    have hzero : Measure.dirac x {y | T y = hT.mk T y}ᶜ = 0 :=
      mem_ae_iff.1 hT.ae_eq_mk
    rw [Measure.dirac_apply_of_mem hmem] at hzero
    exact one_ne_zero hzero
  rw [Measure.map_congr hT.ae_eq_mk, Measure.map_dirac' hT.measurable_mk, ← hx]

/-- The graph plan of an almost everywhere measurable map out of a Dirac measure is the Dirac
measure at the corresponding point of the graph. -/
@[simp]
theorem graphPlan_dirac (hT : AEMeasurable T (Measure.dirac x)) :
    graphPlan (Measure.dirac x) T = Measure.dirac (x, T x) :=
  map_dirac_of_aemeasurable (measurable_id'.aemeasurable.prodMk hT)

/-- **A transport map cannot split an atom**: a map with a law under `δ_x` has the Dirac law at
`T x`. Since `δ_x` is coupled to *every* probability measure by
`TauCeti.isCoupling_map_prodMk`, this is the basic obstruction to solving the Monge problem where
the Kantorovich problem is solvable. -/
theorem eq_dirac_of_hasLaw_dirac (h : HasLaw T ν (Measure.dirac x)) :
    ν = Measure.dirac (T x) :=
  h.map_eq.symm.trans (map_dirac_of_aemeasurable h.aemeasurable)

/-! ### Deterministic plans -/

/-- Almost sure statements about a graph plan are almost sure statements about the source. -/
theorem ae_graphPlan_iff (hT : AEMeasurable T μ) {p : X × Y → Prop}
    (hp : MeasurableSet {z | p z}) :
    (∀ᵐ z ∂graphPlan μ T, p z) ↔ ∀ᵐ x ∂μ, p (x, T x) :=
  ae_map_iff (measurable_id'.aemeasurable.prodMk hT) hp

/-- **A deterministic plan is a graph plan**: a measure on `X × Y` carried by the graph of an
almost everywhere measurable map `T` is the graph plan of `T` under its own first marginal. This
is the converse of `TauCeti.isCoupling_graphPlan`. -/
theorem eq_graphPlan_fst_of_ae (hT : AEMeasurable T π.fst) (h : ∀ᵐ z ∂π, z.2 = T z.1) :
    π = graphPlan π.fst T := by
  have hgraph : (fun z : X × Y ↦ z) =ᵐ[π] fun z ↦ (z.1, T z.1) := by
    filter_upwards [h] with z hz
    rw [← hz]
  calc π = π.map (fun z ↦ z) := Measure.map_id'.symm
    _ = π.map (fun z ↦ (z.1, T z.1)) := Measure.map_congr hgraph
    _ = graphPlan π.fst T :=
        (AEMeasurable.map_map_of_aemeasurable
          (measurable_id'.aemeasurable.prodMk hT) measurable_fst.aemeasurable).symm

/-- A coupling carried by the graph of an almost everywhere measurable map is that map's graph
plan; in particular the map is a transport map from the coupling's source to its target. -/
theorem IsCoupling.eq_graphPlan_of_ae (hπ : IsCoupling π μ ν) (hT : AEMeasurable T μ)
    (h : ∀ᵐ z ∂π, z.2 = T z.1) : π = graphPlan μ T := by
  rw [eq_graphPlan_fst_of_ae (hπ.fst_eq.symm ▸ hT) h, hπ.fst_eq]

/-- A coupling carried by the graph of an almost everywhere measurable map exhibits that map as a
transport map between the coupling's two marginals. -/
theorem IsCoupling.hasLaw_of_ae (hπ : IsCoupling π μ ν) (hT : AEMeasurable T μ)
    (h : ∀ᵐ z ∂π, z.2 = T z.1) : HasLaw T ν μ where
  aemeasurable := hT
  map_eq := by rw [← snd_graphPlan μ T, ← hπ.eq_graphPlan_of_ae hT h, hπ.snd_eq]

/-! ### Composing transport maps -/

/-- Pushing a graph plan forward in its second coordinate composes the map with the graph. -/
theorem map_prodMap_id_graphPlan (hT : AEMeasurable T μ) (hS : Measurable S) :
    (graphPlan μ T).map (Prod.map id S) = graphPlan μ (S ∘ T) :=
  AEMeasurable.map_map_of_aemeasurable (measurable_id'.prodMap hS).aemeasurable
    (measurable_id'.aemeasurable.prodMk hT)

/-! ### The cost of a transport map -/

/-- Integrating against a graph plan is integrating the cost along the graph. -/
theorem lintegral_graphPlan (hT : AEMeasurable T μ) (hc : AEMeasurable c (graphPlan μ T)) :
    ∫⁻ z, c z ∂graphPlan μ T = ∫⁻ x, c (x, T x) ∂μ :=
  lintegral_map' hc (measurable_id'.aemeasurable.prodMk hT)

/-- **The Monge problem dominates the Kantorovich problem**: the transport cost of `μ` and `ν` is
at most the cost of any transport map from `μ` to `ν`, because that map's graph plan is a feasible
coupling. -/
theorem transportCost_le_lintegral_of_hasLaw (hT : HasLaw T ν μ)
    (hc : AEMeasurable c (graphPlan μ T)) :
    transportCost c μ ν ≤ ∫⁻ x, c (x, T x) ∂μ :=
  (transportCost_le_lintegral (isCoupling_graphPlan_of_hasLaw hT) c).trans_eq
    (lintegral_graphPlan hT.aemeasurable hc)

/-- A transport map whose graph plan is optimal solves both the Monge and the Kantorovich problem,
and then the two values agree. -/
theorem lintegral_eq_transportCost_of_isOptimalCoupling (hT : AEMeasurable T μ)
    (hc : AEMeasurable c (graphPlan μ T)) (h : IsOptimalCoupling c (graphPlan μ T) μ ν) :
    ∫⁻ x, c (x, T x) ∂μ = transportCost c μ ν :=
  (lintegral_graphPlan hT hc).symm.trans h.lintegral_eq

/-! ### The bundled graph coupling -/

namespace Coupling

variable {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}

/-- The graph plan of a transport map between two probability measures, as a bundled coupling. -/
def graphPlan (T : X → Y) (hT : HasLaw T ν.toMeasure μ.toMeasure) : Coupling μ ν :=
  ⟨⟨TauCeti.graphPlan μ.toMeasure T, isProbabilityMeasure_graphPlan hT.aemeasurable⟩,
    isCoupling_graphPlan_of_hasLaw hT⟩

@[simp]
theorem coe_graphPlan (T : X → Y) (hT : HasLaw T ν.toMeasure μ.toMeasure) :
    ((graphPlan T hT : Coupling μ ν) : ProbabilityMeasure (X × Y)).toMeasure =
      TauCeti.graphPlan μ.toMeasure T :=
  (rfl)

end Coupling

end TauCeti
