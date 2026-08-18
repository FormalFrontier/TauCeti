/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Graph plans of transport maps

A *transport map* from `μ : Measure X` to `ν : Measure Y` is a map `T : X → Y` pushing `μ` to
`ν`; the predicate for that is Mathlib's `ProbabilityTheory.HasLaw T ν μ`, which asks for
`μ.map T = ν` together with `μ`-a.e. measurability of `T`. This file builds the
optimal-transport interface around it: the *graph plan*

`graphPlan T μ = μ.map fun x ↦ (x, T x)`,

the measure on `X × Y` carried by the graph of `T`. Its second marginal is always `μ.map T`, and
its first marginal is `μ` as soon as `T` is `μ`-a.e. measurable; for such a `T` it is the
Kantorovich plan induced by the Monge map `T`.

## Main definitions

* `Measure.graphPlan` — the plan `μ.map fun x ↦ (x, T x)` induced by `T`.

## Main results

* `Measure.fst_graphPlan` and `Measure.snd_graphPlan` — the first marginal of a
  graph plan is `μ` whenever `T` is `μ`-a.e. measurable, and its second marginal is `μ.map T`;
  when `ProbabilityTheory.HasLaw T ν μ` holds the second one is `ν`
  (`Measure.snd_graphPlan_of_hasLaw`), so every Monge map induces a Kantorovich plan;
* `Measure.lintegral_graphPlan` — integrating against a graph plan is integrating
  `x ↦ f (x, T x)`, the identity turning a Kantorovich cost into a Monge cost;
* `Measure.eq_graphPlan_iff` — a plan is the graph plan of `T` exactly when it is
  concentrated on the graph of `T`: this is the intrinsic description of deterministic plans;
* `Measure.graphPlan_eq_graphPlan_iff` — two maps induce the same plan exactly when they
  agree `μ`-a.e., so a transport map is pinned down by its plan only up to a null set.

That the Monge problem is genuinely infeasible for some data — a Dirac source can only be
transported onto a Dirac target — is not about graph plans and lives with the other
`ProbabilityTheory.HasLaw` facts, in
`TauCeti.Probability.not_hasLaw_dirac_source_of_forall_ne_dirac`.

## Conventions

Following `TauCetiRoadmap/OptimalTransport/README.md`, no parallel `IsTransportMap` predicate is
introduced: feasibility of a map is `ProbabilityTheory.HasLaw`, and equality or uniqueness of
transport maps is always stated `μ`-a.e. Everything lives at the level of arbitrary measures on
arbitrary measurable spaces; no topology, density, or normalization is involved.

Recognizing a graph needs the diagonal of `Y × Y` to be measurable, i.e. the `MeasurableEq Y`
typeclass, which holds for standard Borel spaces and, more generally, for second-countable `T2`
topological spaces whose measurable structure is compatible with the topology, in the sense of
`OpensMeasurableSpace` (so in particular for the Borel structure). That hypothesis is stated only
where it is used.

## References

* Roadmap: `TauCetiRoadmap/OptimalTransport/README.md`, Layer 0, item 2 (transport maps and the
  graph coupling interface around `ProbabilityTheory.HasLaw`).
* C. Villani, *Optimal Transport: Old and New*, Chapter 1 (the Monge and Kantorovich problems,
  and the passage from a map to a plan).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace Measure

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The **graph plan** of a map `T : X → Y` over a measure `μ` on `X`: the pushforward of `μ`
along `x ↦ (x, T x)`, that is, the measure on `X × Y` carried by the graph of `T`.

Its second marginal is `μ.map T` (`Measure.snd_graphPlan`), and its first marginal is `μ`
as soon as `T` is `μ`-a.e. measurable (`Measure.fst_graphPlan`); for such a `T` this is
the Kantorovich plan induced by the Monge map `T`. -/
def graphPlan (T : X → Y) (μ : Measure X) : Measure (X × Y) :=
  μ.map fun x ↦ (x, T x)

variable {T S : X → Y} {μ : Measure X} {ν : Measure Y}

/-- The defining equation of `Measure.graphPlan`. -/
theorem graphPlan_def (T : X → Y) (μ : Measure X) : graphPlan T μ = μ.map fun x ↦ (x, T x) :=
  (rfl)

/-- The map `x ↦ (x, T x)` onto the graph of `T` is a.e. measurable as soon as `T` is. -/
private theorem aemeasurable_prodMk_self (hT : AEMeasurable T μ) :
    AEMeasurable (fun x ↦ (x, T x)) μ :=
  aemeasurable_id.prodMk hT

/-- The map `x ↦ (x, T x)` onto the graph of `T` is measurable as soon as `T` is. -/
private theorem measurable_prodMk_self (hT : Measurable T) : Measurable fun x ↦ (x, T x) :=
  measurable_id.prodMk hT

/-- A graph plan inherits `MeasureTheory.SFinite` from its source measure, as a pushforward
does; this is what consumers such as `MeasureTheory.Measure.compProd` ask for. -/
instance instSFiniteGraphPlan [SFinite μ] : SFinite (graphPlan T μ) := by
  rw [graphPlan_def]; infer_instance

/-- A graph plan inherits `MeasureTheory.IsFiniteMeasure` from its source measure, as a
pushforward does. -/
instance instIsFiniteMeasureGraphPlan [IsFiniteMeasure μ] : IsFiniteMeasure (graphPlan T μ) := by
  rw [graphPlan_def]; infer_instance

/-- A graph plan measures a set by the source points whose graph point lies in it. -/
theorem graphPlan_apply (hT : AEMeasurable T μ) {s : Set (X × Y)} (hs : MeasurableSet s) :
    graphPlan T μ s = μ {x | (x, T x) ∈ s} :=
  Measure.map_apply_of_aemeasurable (aemeasurable_prodMk_self hT) hs

/-- The graph plan over the zero measure is the zero measure. -/
@[simp]
theorem graphPlan_zero (T : X → Y) : graphPlan T (0 : Measure X) = 0 :=
  Measure.map_zero _

/-- The first marginal of a graph plan is the source measure. -/
@[simp]
theorem fst_graphPlan (hT : AEMeasurable T μ) : (graphPlan T μ).fst = μ := by
  rw [graphPlan, Measure.fst_map_prodMk₀ hT, Measure.map_id']

/-- The second marginal of a graph plan is the pushforward of the source measure. -/
@[simp]
theorem snd_graphPlan (T : X → Y) (μ : Measure X) : (graphPlan T μ).snd = μ.map T :=
  Measure.snd_map_prodMk₀ aemeasurable_id

/-- A graph plan over a probability measure is a probability measure. -/
theorem isProbabilityMeasure_graphPlan [IsProbabilityMeasure μ] (hT : AEMeasurable T μ) :
    IsProbabilityMeasure (graphPlan T μ) :=
  Measure.isProbabilityMeasure_map (aemeasurable_prodMk_self hT)

/-- Integration against a graph plan is integration of the composite `x ↦ f (x, T x)`.

This is the identity rewriting the Kantorovich cost of a graph plan as the Monge cost of the
underlying map. -/
theorem lintegral_graphPlan (hT : AEMeasurable T μ) {f : X × Y → ℝ≥0∞}
    (hf : AEMeasurable f (graphPlan T μ)) :
    ∫⁻ z, f z ∂graphPlan T μ = ∫⁻ x, f (x, T x) ∂μ :=
  lintegral_map' hf (aemeasurable_prodMk_self hT)

/-! ### Feasibility: transport maps and the plans they induce -/

/-- A map is a transport map from `μ` to `ν` exactly when the second marginal of its graph plan
is `ν`. -/
theorem hasLaw_iff_snd_graphPlan_eq (hT : AEMeasurable T μ) :
    HasLaw T ν μ ↔ (graphPlan T μ).snd = ν := by
  rw [snd_graphPlan]
  exact ⟨fun h ↦ h.map_eq, fun h ↦ ⟨hT, h⟩⟩

/-- The second marginal of the graph plan of a transport map from `μ` to `ν` is `ν`; together
with `Measure.fst_graphPlan` this is the passage from a Monge map to a Kantorovich
plan. -/
theorem snd_graphPlan_of_hasLaw (hT : HasLaw T ν μ) : (graphPlan T μ).snd = ν := by
  rw [snd_graphPlan, hT.map_eq]

/-- Chaining two transport maps chains the targets of their graph plans. -/
theorem snd_graphPlan_comp {R : Y → Z} {ρ : Measure Z} (hR : HasLaw R ρ ν) (hT : HasLaw T ν μ) :
    (graphPlan (R ∘ T) μ).snd = ρ :=
  snd_graphPlan_of_hasLaw (hR.comp hT)

/-- A measure-preserving map is in particular a transport map, so the second marginal of its
graph plan is the prescribed target. This covers measure-preserving equivalences. -/
theorem snd_graphPlan_of_measurePreserving (hT : MeasurePreserving T μ ν) :
    (graphPlan T μ).snd = ν :=
  snd_graphPlan_of_hasLaw hT.hasLaw

/-- The identity transports `μ` to itself, so the second marginal of its graph plan is `μ`. -/
theorem snd_graphPlan_id (μ : Measure X) : (graphPlan (id : X → X) μ).snd = μ :=
  snd_graphPlan_of_hasLaw HasLaw.id

/-! ### Elementary functoriality -/

/-- `μ`-a.e. equal maps induce the same graph plan. -/
theorem graphPlan_congr (h : T =ᵐ[μ] S) : graphPlan T μ = graphPlan S μ :=
  Measure.map_congr <| by filter_upwards [h] with x hx; rw [hx]

/-- Taking the graph plan of a fixed map is additive in the source measure. -/
@[simp]
theorem graphPlan_add {μ₁ μ₂ : Measure X} (hT₁ : AEMeasurable T μ₁) (hT₂ : AEMeasurable T μ₂) :
    graphPlan T (μ₁ + μ₂) = graphPlan T μ₁ + graphPlan T μ₂ :=
  AEMeasurable.map_add₀ (aemeasurable_prodMk_self hT₁) (aemeasurable_prodMk_self hT₂)

/-- Taking the graph plan of a fixed map commutes with rescaling the source measure by an
extended nonnegative real. -/
@[simp]
theorem graphPlan_smul (T : X → Y) (c : ℝ≥0∞) (μ : Measure X) :
    graphPlan T (c • μ) = c • graphPlan T μ :=
  Measure.map_smul _ _ _

/-- The graph plan over a Dirac measure is the Dirac measure at the corresponding graph point. -/
@[simp]
theorem graphPlan_dirac {x : X} (hT : AEMeasurable T (Measure.dirac x)) :
    graphPlan T (Measure.dirac x) = Measure.dirac (x, T x) :=
  map_dirac_of_aemeasurable (aemeasurable_prodMk_self hT)

/-- Postcomposing a transport map pushes the graph plan through the second coordinate. -/
theorem graphPlan_comp {R : Y → Z} (hT : AEMeasurable T μ) (hR : AEMeasurable R (μ.map T)) :
    graphPlan (R ∘ T) μ = (graphPlan T μ).map (Prod.map id R) := by
  have hR' : AEMeasurable R (graphPlan T μ).snd := by rwa [snd_graphPlan]
  have hmap : AEMeasurable (Prod.map (id : X → X) R) (μ.map fun x ↦ (x, T x)) :=
    measurable_fst.aemeasurable.prodMk (hR'.comp_aemeasurable' measurable_snd.aemeasurable)
  simp only [graphPlan]
  rw [AEMeasurable.map_map_of_aemeasurable hmap (aemeasurable_prodMk_self hT)]
  simp [Function.comp_def, Prod.map]

/-- Reparametrizing the source measure pushes the graph plan through the first coordinate. -/
theorem graphPlan_map {f : Z → X} {μ : Measure Z} (hf : AEMeasurable f μ)
    (hT : AEMeasurable T (μ.map f)) :
    graphPlan T (μ.map f) = (graphPlan (T ∘ f) μ).map (Prod.map f id) := by
  have hTf : AEMeasurable (T ∘ f) μ := hT.comp_aemeasurable hf
  have hf' : AEMeasurable f (graphPlan (T ∘ f) μ).fst := by rwa [fst_graphPlan hTf]
  have hmap : AEMeasurable (Prod.map f (id : Y → Y)) (μ.map fun z ↦ (z, (T ∘ f) z)) :=
    (hf'.comp_aemeasurable' measurable_fst.aemeasurable).prodMk measurable_snd.aemeasurable
  simp only [graphPlan]
  rw [AEMeasurable.map_map_of_aemeasurable (aemeasurable_prodMk_self hT) hf,
    AEMeasurable.map_map_of_aemeasurable hmap (aemeasurable_prodMk_self hTf)]
  simp [Function.comp_def, Prod.map]

/-- Swapping the coordinates of a graph plan gives the cograph plan. -/
theorem map_swap_graphPlan (hT : AEMeasurable T μ) :
    (graphPlan T μ).map Prod.swap = μ.map fun x ↦ (T x, x) := by
  rw [graphPlan, AEMeasurable.map_map_of_aemeasurable measurable_swap.aemeasurable
    (aemeasurable_prodMk_self hT)]
  simp [Function.comp_def, Prod.swap]

/-- A measurable equivalence and its inverse have graph plans exchanged by the coordinate
swap. -/
theorem map_swap_graphPlan_symm (e : X ≃ᵐ Y) (μ : Measure X) :
    (graphPlan e μ).map Prod.swap = graphPlan e.symm (μ.map e) := by
  rw [map_swap_graphPlan e.measurable.aemeasurable, graphPlan,
    Measure.map_map (measurable_prodMk_self e.symm.measurable) e.measurable]
  simp [Function.comp_def]

/-! ### Deterministic plans: concentration on a graph -/

/-- A graph plan is concentrated on the graph of its map. -/
theorem graphPlan_ae_snd_eq [MeasurableEq Y] (hT : AEMeasurable T μ) :
    ∀ᵐ z ∂graphPlan T μ, z.2 = T z.1 := by
  have hmk : ∀ᵐ z ∂graphPlan T μ, z.2 = hT.mk T z.1 := by
    rw [graphPlan_congr hT.ae_eq_mk]
    exact (ae_map_iff (measurable_prodMk_self hT.measurable_mk).aemeasurable
      (measurableSet_eq_fun measurable_snd (hT.measurable_mk.comp measurable_fst))).2
      (ae_of_all _ fun _ ↦ rfl)
  have hfst : Measure.QuasiMeasurePreserving Prod.fst (graphPlan T μ) μ :=
    ⟨measurable_fst, (fst_graphPlan hT).le.absolutelyContinuous⟩
  filter_upwards [hmk, hfst.ae hT.ae_eq_mk] with z hz hz'
  rw [hz, ← hz']

/-- The graph plan of `T` is concentrated on the graph of `S` exactly when `S` agrees with `T`
almost everywhere. -/
theorem graphPlan_ae_snd_eq_iff [MeasurableEq Y] (hT : AEMeasurable T μ) (hS : AEMeasurable S μ) :
    (∀ᵐ z ∂graphPlan T μ, z.2 = S z.1) ↔ T =ᵐ[μ] S := by
  have hfst : Measure.QuasiMeasurePreserving Prod.fst (graphPlan T μ) μ :=
    ⟨measurable_fst, (fst_graphPlan hT).le.absolutelyContinuous⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hmk : ∀ᵐ z ∂graphPlan (hT.mk T) μ, z.2 = hS.mk S z.1 := by
      rw [← graphPlan_congr hT.ae_eq_mk]
      filter_upwards [h, hfst.ae hS.ae_eq_mk] with z hz hz'
      rw [hz, hz']
    have key : hT.mk T =ᵐ[μ] hS.mk S :=
      (ae_map_iff (measurable_prodMk_self hT.measurable_mk).aemeasurable
        (measurableSet_eq_fun measurable_snd (hS.measurable_mk.comp measurable_fst))).1 hmk
    exact hT.ae_eq_mk.trans (key.trans hS.ae_eq_mk.symm)
  · filter_upwards [graphPlan_ae_snd_eq hT, hfst.ae h] with z hz hz'
    rw [hz, hz']

/-- A plan concentrated on the graph of `T` is the graph plan of `T` over its own first
marginal. -/
theorem eq_graphPlan_of_ae_snd_eq {π : Measure (X × Y)} (hT : AEMeasurable T π.fst)
    (h : ∀ᵐ z ∂π, z.2 = T z.1) : π = graphPlan T π.fst := by
  have hae : (id : X × Y → X × Y) =ᵐ[π] fun z ↦ (z.1, T z.1) := by
    filter_upwards [h] with z hz
    rw [id_eq, ← hz]
  calc π = π.map id := Measure.map_id.symm
    _ = π.map fun z ↦ (z.1, T z.1) := Measure.map_congr hae
    _ = (π.map Prod.fst).map fun x ↦ (x, T x) :=
        (AEMeasurable.map_map_of_aemeasurable (aemeasurable_prodMk_self hT)
          measurable_fst.aemeasurable).symm
    _ = graphPlan T π.fst := by rw [graphPlan_def, Measure.fst]

/-- **The deterministic plans are exactly the plans carried by a graph.** A plan on `X × Y` is
the graph plan of an a.e. measurable `T` over its own first marginal precisely when its second
coordinate almost everywhere equals `T` of its first coordinate. -/
theorem eq_graphPlan_iff [MeasurableEq Y] {π : Measure (X × Y)} (hT : AEMeasurable T π.fst) :
    π = graphPlan T π.fst ↔ ∀ᵐ z ∂π, z.2 = T z.1 := by
  refine ⟨fun h ↦ ?_, eq_graphPlan_of_ae_snd_eq hT⟩
  rw [h]
  exact graphPlan_ae_snd_eq hT

/-- **A transport map is pinned down by its plan only up to a null set.** Two `μ`-a.e. measurable
maps induce the same graph plan over `μ` exactly when they agree `μ`-almost everywhere. -/
theorem graphPlan_eq_graphPlan_iff [MeasurableEq Y] (hT : AEMeasurable T μ)
    (hS : AEMeasurable S μ) : graphPlan T μ = graphPlan S μ ↔ T =ᵐ[μ] S := by
  refine ⟨fun h ↦ (graphPlan_ae_snd_eq_iff hT hS).1 ?_, graphPlan_congr⟩
  rw [h]
  exact graphPlan_ae_snd_eq hS

end Measure
