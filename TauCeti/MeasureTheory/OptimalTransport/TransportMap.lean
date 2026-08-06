/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Graph plans of transport maps

A *transport map* from `μ : Measure X` to `ν : Measure Y` is a map `T : X → Y` pushing `μ` to
`ν`; the predicate for that is Mathlib's `ProbabilityTheory.HasLaw T ν μ`, which asks for
`μ.map T = ν` together with `μ`-a.e. measurability of `T`. This file builds the
optimal-transport interface around it: the *graph plan*

`graphPlan T μ = μ.map fun x ↦ (x, T x)`,

the measure on `X × Y` carried by the graph of `T`. It is the Kantorovich plan induced by the
Monge map `T`.

## Main definitions

* `TauCeti.Measure.graphPlan` — the plan `μ.map fun x ↦ (x, T x)` induced by `T`.

## Main results

* `TauCeti.Measure.fst_graphPlan` and `TauCeti.Measure.snd_graphPlan` — the marginals of a graph
  plan are `μ` and `μ.map T`; when `ProbabilityTheory.HasLaw T ν μ` holds the second one is `ν`
  (`TauCeti.Measure.snd_graphPlan_of_hasLaw`), so every Monge map induces a Kantorovich plan;
* `TauCeti.Measure.lintegral_graphPlan` — integrating against a graph plan is integrating
  `x ↦ f (x, T x)`, the identity turning a Kantorovich cost into a Monge cost;
* `TauCeti.Measure.eq_graphPlan_iff` — a plan is the graph plan of `T` exactly when it is
  concentrated on the graph of `T`: this is the intrinsic description of deterministic plans;
* `TauCeti.Measure.graphPlan_eq_graphPlan_iff` — two maps induce the same plan exactly when they
  agree `μ`-a.e., so a transport map is pinned down by its plan only up to a null set;
* `TauCeti.Measure.hasLaw_dirac_iff` and `TauCeti.Measure.not_hasLaw_dirac_of_forall_ne` — a
  Dirac source can only be transported onto a Dirac target, so for some data the Monge problem
  has no solution at all even though plans always exist.

## Conventions

Following `TauCetiRoadmap/OptimalTransport/README.md`, no parallel `IsTransportMap` predicate is
introduced: feasibility of a map is `ProbabilityTheory.HasLaw`, and equality or uniqueness of
transport maps is always stated `μ`-a.e. Everything lives at the level of arbitrary measures on
arbitrary measurable spaces; no topology, density, or normalization is involved.

Recognizing a graph needs the diagonal of `Y × Y` to be measurable, i.e. the `MeasurableEq Y`
typeclass, which holds for standard Borel spaces and, more generally, for second-countable `T2`
spaces. That hypothesis is stated only where it is used.

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

namespace TauCeti

namespace Measure

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The **graph plan** of a map `T : X → Y` over a measure `μ` on `X`: the pushforward of `μ`
along `x ↦ (x, T x)`, that is, the measure on `X × Y` carried by the graph of `T`.

This is the Kantorovich plan induced by the Monge map `T`; its marginals are `μ` and `μ.map T`
(`TauCeti.Measure.fst_graphPlan`, `TauCeti.Measure.snd_graphPlan`). -/
@[expose]
def graphPlan (T : X → Y) (μ : Measure X) : Measure (X × Y) :=
  μ.map fun x ↦ (x, T x)

variable {T S : X → Y} {μ : Measure X} {ν : Measure Y}

theorem graphPlan_def (T : X → Y) (μ : Measure X) : graphPlan T μ = μ.map fun x ↦ (x, T x) :=
  rfl

/-- The graph map `x ↦ (x, T x)` is a.e. measurable as soon as `T` is. -/
theorem aemeasurable_graphMap (hT : AEMeasurable T μ) : AEMeasurable (fun x ↦ (x, T x)) μ :=
  aemeasurable_id.prodMk hT

/-- The graph map `x ↦ (x, T x)` is measurable as soon as `T` is. -/
theorem measurable_graphMap (hT : Measurable T) : Measurable fun x ↦ (x, T x) :=
  measurable_id.prodMk hT

/-- A graph plan measures a set by the source points whose graph point lies in it. -/
theorem graphPlan_apply (hT : AEMeasurable T μ) {s : Set (X × Y)} (hs : MeasurableSet s) :
    graphPlan T μ s = μ {x | (x, T x) ∈ s} :=
  Measure.map_apply_of_aemeasurable (aemeasurable_graphMap hT) hs

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
  Measure.isProbabilityMeasure_map (aemeasurable_graphMap hT)

/-- Integration against a graph plan is integration of the composite `x ↦ f (x, T x)`.

This is the identity rewriting the Kantorovich cost of a graph plan as the Monge cost of the
underlying map. -/
theorem lintegral_graphPlan (hT : AEMeasurable T μ) {f : X × Y → ℝ≥0∞}
    (hf : AEMeasurable f (graphPlan T μ)) :
    ∫⁻ z, f z ∂graphPlan T μ = ∫⁻ x, f (x, T x) ∂μ :=
  lintegral_map' hf (aemeasurable_graphMap hT)

/-! ### Feasibility: transport maps and the plans they induce -/

/-- A map is a transport map from `μ` to `ν` exactly when the second marginal of its graph plan
is `ν`. -/
theorem hasLaw_iff_snd_graphPlan (hT : AEMeasurable T μ) :
    HasLaw T ν μ ↔ (graphPlan T μ).snd = ν := by
  rw [snd_graphPlan]
  exact ⟨fun h ↦ h.map_eq, fun h ↦ ⟨hT, h⟩⟩

/-- **A Monge map induces a Kantorovich plan**: the first marginal of the graph plan of a
transport map from `μ` to `ν` is `μ`. -/
theorem fst_graphPlan_of_hasLaw (hT : HasLaw T ν μ) : (graphPlan T μ).fst = μ :=
  fst_graphPlan hT.aemeasurable

/-- **A Monge map induces a Kantorovich plan**: the second marginal of the graph plan of a
transport map from `μ` to `ν` is `ν`. -/
theorem snd_graphPlan_of_hasLaw (hT : HasLaw T ν μ) : (graphPlan T μ).snd = ν := by
  rw [snd_graphPlan, hT.map_eq]

/-- Chaining two transport maps chains the targets of their graph plans. -/
theorem snd_graphPlan_comp {R : Y → Z} {ρ : Measure Z} (hR : HasLaw R ρ ν) (hT : HasLaw T ν μ) :
    (graphPlan (R ∘ T) μ).snd = ρ :=
  snd_graphPlan_of_hasLaw (hR.comp hT)

/-- A measure-preserving map is in particular a transport map, so its graph plan has the
prescribed marginals. This covers measurable equivalences between measure spaces. -/
theorem snd_graphPlan_of_measurePreserving (hT : MeasurePreserving T μ ν) :
    (graphPlan T μ).snd = ν :=
  snd_graphPlan_of_hasLaw hT.hasLaw

/-- The identity transports `μ` to itself, and its graph plan is the diagonal plan. -/
theorem snd_graphPlan_id (μ : Measure X) : (graphPlan (id : X → X) μ).snd = μ :=
  snd_graphPlan_of_hasLaw HasLaw.id

/-! ### Elementary functoriality -/

/-- `μ`-a.e. equal maps induce the same graph plan. -/
theorem graphPlan_congr (h : T =ᵐ[μ] S) : graphPlan T μ = graphPlan S μ :=
  Measure.map_congr <| by filter_upwards [h] with x hx; rw [hx]

@[simp]
theorem graphPlan_add (hT : Measurable T) (μ₁ μ₂ : Measure X) :
    graphPlan T (μ₁ + μ₂) = graphPlan T μ₁ + graphPlan T μ₂ :=
  Measure.map_add _ _ (measurable_graphMap hT)

@[simp]
theorem graphPlan_smul (T : X → Y) (c : ℝ≥0∞) (μ : Measure X) :
    graphPlan T (c • μ) = c • graphPlan T μ :=
  Measure.map_smul _ _ _

/-- The graph plan over a Dirac measure is the Dirac measure at the corresponding graph point. -/
@[simp]
theorem graphPlan_dirac (hT : Measurable T) (x : X) :
    graphPlan T (Measure.dirac x) = Measure.dirac (x, T x) :=
  Measure.map_dirac' (measurable_graphMap hT) x

/-- The graph plan of the identity is the diagonal plan. -/
theorem graphPlan_id (μ : Measure X) : graphPlan id μ = μ.map fun x ↦ (x, x) := rfl

/-- The graph plan of the identity is the composition-product with the identity kernel. -/
theorem graphPlan_id_eq_compProd (μ : Measure X) [SFinite μ] : graphPlan id μ = μ ⊗ₘ Kernel.id :=
  Measure.compProd_id.symm

/-- A graph plan is the composition-product of its source measure with the deterministic kernel
of the map. This is what singles out the graph plans among all plans disintegrated over their
first marginal. -/
theorem graphPlan_eq_compProd_deterministic (hT : Measurable T) (μ : Measure X) [SFinite μ] :
    graphPlan T μ = μ ⊗ₘ Kernel.deterministic T hT :=
  (Measure.compProd_deterministic hT).symm

/-- Postcomposing a transport map pushes the graph plan through the second coordinate. -/
theorem graphPlan_comp {R : Y → Z} (hT : AEMeasurable T μ) (hR : Measurable R) :
    graphPlan (R ∘ T) μ = (graphPlan T μ).map (Prod.map id R) := by
  simp only [graphPlan]
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_id.prodMap hR).aemeasurable
    (aemeasurable_graphMap hT)]
  rfl

/-- Reparametrizing the source measure pushes the graph plan through the first coordinate. -/
theorem graphPlan_map {f : Z → X} (hf : Measurable f) (hT : Measurable T) (μ : Measure Z) :
    graphPlan T (μ.map f) = (graphPlan (T ∘ f) μ).map (Prod.map f id) := by
  simp only [graphPlan]
  rw [Measure.map_map (measurable_graphMap hT) hf,
    Measure.map_map (hf.prodMap measurable_id) (measurable_graphMap (hT.comp hf))]
  rfl

/-- Swapping the coordinates of a graph plan gives the cograph plan. -/
theorem map_swap_graphPlan (hT : Measurable T) (μ : Measure X) :
    (graphPlan T μ).map Prod.swap = μ.map fun x ↦ (T x, x) := by
  rw [graphPlan, Measure.map_map measurable_swap (measurable_graphMap hT)]
  rfl

/-- A measurable equivalence and its inverse have graph plans exchanged by the coordinate
swap. -/
theorem map_swap_graphPlan_measurableEquiv (e : X ≃ᵐ Y) (μ : Measure X) :
    (graphPlan e μ).map Prod.swap = graphPlan e.symm (μ.map e) := by
  rw [map_swap_graphPlan e.measurable, graphPlan,
    Measure.map_map (measurable_graphMap e.symm.measurable) e.measurable]
  simp [Function.comp_def]

/-! ### Deterministic plans: concentration on a graph -/

/-- A graph plan is concentrated on the graph of its map. -/
theorem ae_snd_eq_of_graphPlan [MeasurableEq Y] (hT : Measurable T) (μ : Measure X) :
    ∀ᵐ z ∂graphPlan T μ, z.2 = T z.1 :=
  (ae_map_iff (measurable_graphMap hT).aemeasurable
    (measurableSet_eq_fun measurable_snd (hT.comp measurable_fst))).2 (ae_of_all _ fun _ ↦ rfl)

/-- A plan concentrated on the graph of `T` is the graph plan of `T` over its own first
marginal. -/
theorem eq_graphPlan_of_ae {π : Measure (X × Y)} (hT : AEMeasurable T π.fst)
    (h : ∀ᵐ z ∂π, z.2 = T z.1) : π = graphPlan T π.fst := by
  have hae : (id : X × Y → X × Y) =ᵐ[π] fun z ↦ (z.1, T z.1) := by
    filter_upwards [h] with z hz
    rw [id_eq, ← hz]
  calc π = π.map id := Measure.map_id.symm
    _ = π.map fun z ↦ (z.1, T z.1) := Measure.map_congr hae
    _ = (π.map Prod.fst).map fun x ↦ (x, T x) :=
        (AEMeasurable.map_map_of_aemeasurable (aemeasurable_graphMap hT)
          measurable_fst.aemeasurable).symm
    _ = graphPlan T π.fst := rfl

/-- **The deterministic plans are exactly the plans carried by a graph.** A plan on `X × Y` is
the graph plan of a measurable `T` over its own first marginal precisely when its second
coordinate almost everywhere equals `T` of its first coordinate. -/
theorem eq_graphPlan_iff [MeasurableEq Y] {π : Measure (X × Y)} (hT : Measurable T) :
    π = graphPlan T π.fst ↔ ∀ᵐ z ∂π, z.2 = T z.1 := by
  refine ⟨fun h ↦ ?_, eq_graphPlan_of_ae hT.aemeasurable⟩
  rw [h]
  exact ae_snd_eq_of_graphPlan hT π.fst

/-- **A transport map is pinned down by its plan only up to a null set.** Two measurable maps
induce the same graph plan over `μ` exactly when they agree `μ`-almost everywhere. -/
theorem graphPlan_eq_graphPlan_iff [MeasurableEq Y] (hT : Measurable T) (hS : Measurable S)
    (μ : Measure X) : graphPlan T μ = graphPlan S μ ↔ T =ᵐ[μ] S := by
  refine ⟨fun h ↦ ?_, graphPlan_congr⟩
  have hae : ∀ᵐ z ∂graphPlan T μ, z.2 = S z.1 := by
    rw [h]; exact ae_snd_eq_of_graphPlan hS μ
  exact (ae_map_iff (measurable_graphMap hT).aemeasurable
    (measurableSet_eq_fun measurable_snd (hS.comp measurable_fst))).1 hae

/-! ### A Dirac source admits no non-Dirac transport map -/

/-- A measurable map transports a Dirac measure exactly onto the Dirac measure at its value. -/
theorem hasLaw_dirac_iff (hT : Measurable T) (x : X) :
    HasLaw T ν (Measure.dirac x) ↔ ν = Measure.dirac (T x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨hT.aemeasurable, ?_⟩⟩
  · rw [← h.map_eq, Measure.map_dirac' hT]
  · rw [Measure.map_dirac' hT, h]

/-- **The Monge problem can be infeasible.** No measurable map transports a Dirac measure onto a
target that is not itself a Dirac measure, although plans for such data still exist: the graph
plans are a proper subfamily of all plans. -/
theorem not_hasLaw_dirac_of_forall_ne (hν : ∀ y : Y, ν ≠ Measure.dirac y) (hT : Measurable T)
    (x : X) : ¬HasLaw T ν (Measure.dirac x) :=
  fun h ↦ hν (T x) ((hasLaw_dirac_iff hT x).1 h)

end Measure

end TauCeti
