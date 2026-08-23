/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Probability.HasLaw
public import TauCeti.MeasureTheory.OptimalTransport.Coupling

/-!
# Graph plans: the transport plan induced by a transport map

A *transport map* from `μ` to `ν` is a map `T : X → Y` that pushes `μ` forward to `ν`. Mathlib
already has the predicate for this, `ProbabilityTheory.HasLaw T ν μ`, which asks for
`μ`-almost-everywhere measurability of `T` together with `μ.map T = ν`; this file adds no second
predicate. What it adds is the optimal-transport interface around it: the *graph plan*
`TauCeti.graphPlan T μ`, the pushforward of `μ` along `x ↦ (x, T x)`, which is the transport
plan that moves all the mass sitting at `x` to the single point `T x`.

Two facts organise the file. First, `TauCeti.isCoupling_graphPlan_iff`: for an
almost-everywhere measurable `T`, the graph plan couples `μ` and `ν` exactly when `T` is a
transport map from `μ` to `ν`. This is the passage from the Monge problem to the Kantorovich
problem, whose effect on values is the change of variables `TauCeti.lintegral_graphPlan`; the
resulting inequality of transport costs belongs to the cost theory and is stated in
`TauCeti/MeasureTheory/OptimalTransport/Cost.lean`. Second, `TauCeti.eq_graphPlan_iff`: a plan
is a graph plan exactly when it is *deterministic*, that is, concentrated on the graph of `T`.
With `TauCeti.graphPlan_eq_graphPlan_iff`, which says that the map is determined `μ`-almost
everywhere by its graph plan, this makes the graph construction a bijection between transport
maps modulo `μ`-a.e. equality and deterministic plans.

Nothing here needs a topology, a metric or a normalisation, and the two factors are arbitrary
measurable spaces. The determinism statements do ask that the diagonal of `Y × Y` be
measurable, `MeasurableEq Y`, because "`π` is carried by the graph of `T`" is otherwise not a
statement about a measurable set. That hypothesis holds for every standard Borel space, every
second-countable Hausdorff space with measurable open sets and every countable measurable space
with measurable singletons.

## Main definitions

* `TauCeti.graphPlan T μ` — the graph plan, or Monge plan, of `T`: the pushforward of `μ` along
  `x ↦ (x, T x)`;
* `TauCeti.Coupling.graph` — the graph plan of a transport map between two probability
  measures, bundled as an element of `TauCeti.Coupling`.

## Main statements

* `TauCeti.fst_graphPlan` and `TauCeti.snd_graphPlan` — the two marginals of a graph plan are
  `μ` and `μ.map T`;
* `TauCeti.isCoupling_graphPlan_iff` — the graph plan of an a.e. measurable `T` couples `μ` and
  `ν` exactly when `ProbabilityTheory.HasLaw T ν μ`;
* `TauCeti.lintegral_graphPlan` — the change of variables
  `∫⁻ z, c z ∂graphPlan T μ = ∫⁻ x, c (x, T x) ∂μ`, which feeds the Monge-to-Kantorovich
  inequality `TauCeti.transportCost_le_lintegral_of_hasLaw` in
  `TauCeti/MeasureTheory/OptimalTransport/Cost.lean`;
* `TauCeti.eq_graphPlan_iff` — a plan is the graph plan of `T` exactly when it is concentrated
  on the graph of `T`, with `TauCeti.graphPlan_eq_graphPlan_iff` the uniqueness of the map that
  induces a given deterministic plan;
* `TauCeti.eq_dirac_of_hasLaw_dirac` — a transport map out of a Dirac measure forces the target
  to be a Dirac measure, so the unique plan out of an atom is deterministic only in that case.

## Implementation notes

`TauCeti.graphPlan` records the map in the *second* coordinate, matching the plan-first
convention of `TauCeti.IsCoupling π μ ν`, in which the source is the first factor. The opposite
convention is available as `TauCeti.map_swap_graphPlan`, which identifies the coordinate swap
of a graph plan with the pushforward along `x ↦ (T x, x)`.

Measurability hypotheses are `AEMeasurable` rather than `Measurable` throughout, because that
is what `ProbabilityTheory.HasLaw` supplies and what the pushforward really uses. The two
marginal formulas are asymmetric in this respect: `TauCeti.snd_graphPlan` holds for every `T`
whatsoever, since a `T` that is not a.e. measurable makes both sides the zero measure, while
`TauCeti.fst_graphPlan` genuinely needs `T` to be a.e. measurable.

This module needs nothing from the transport cost, so it sits below it: the Monge-to-Kantorovich
relaxation inequality of Layer 4, item 1, which the change of variables here supplies, is stated
with the cost itself in `TauCeti/MeasureTheory/OptimalTransport/Cost.lean`.

This is Layer 0, item 2 of the optimal-transport roadmap.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, 2009, Chapter 1: a coupling is
  called deterministic when it is of the form `(id, T)_# μ`, and the discussion following
  Definition 1.2 records that this happens exactly when the coupling is concentrated on the
  graph of a map.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §1.1.1, where the Monge problem is relaxed to the Kantorovich problem precisely by sending a
  transport map to its graph plan.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {T S : X → Y} {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)} {c : X × Y → ℝ≥0∞}

/-- The **graph plan**, or Monge plan, of a map `T : X → Y` and a measure `μ` on `X`: the
pushforward of `μ` along `x ↦ (x, T x)`. It is the transport plan that sends all the mass at
`x` to the single point `T x`; `TauCeti.isCoupling_graphPlan_iff` says that it couples `μ` and
`ν` exactly when `T` pushes `μ` forward to `ν`. -/
def graphPlan (T : X → Y) (μ : Measure X) : Measure (X × Y) :=
  μ.map fun x ↦ (x, T x)

/-- The graph plan is the pushforward along the graph map. The definition's body is not exposed,
so this is the lemma downstream modules should rewrite with. -/
theorem graphPlan_def (T : X → Y) (μ : Measure X) :
    graphPlan T μ = μ.map fun x ↦ (x, T x) := (rfl)

/-- The graph map `x ↦ (x, T x)` is a.e. measurable as soon as `T` is. -/
theorem aemeasurable_prodMk_self (hT : AEMeasurable T μ) :
    AEMeasurable (fun x ↦ (x, T x)) μ :=
  aemeasurable_id.prodMk hT

/-- The graph plan of a measurable set is the mass of the set of points whose graph point lies
in it. -/
theorem graphPlan_apply (hT : AEMeasurable T μ) {s : Set (X × Y)} (hs : MeasurableSet s) :
    graphPlan T μ s = μ {x | (x, T x) ∈ s} :=
  Measure.map_apply_of_aemeasurable (aemeasurable_prodMk_self hT) hs

/-- The graph plan of a measurable rectangle is the mass of the part of its base that `T` maps
into its height. -/
theorem graphPlan_prod (hT : AEMeasurable T μ) {s : Set X} {t : Set Y}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    graphPlan T μ (s ×ˢ t) = μ (s ∩ T ⁻¹' t) :=
  graphPlan_apply hT (hs.prod ht)

/-- The second marginal of the graph plan of `T` is the pushforward of `μ` along `T`. No
measurability is needed: if `T` is not a.e. measurable then both sides are the zero measure. -/
@[simp]
theorem snd_graphPlan (T : X → Y) (μ : Measure X) : (graphPlan T μ).snd = μ.map T :=
  Measure.snd_map_prodMk₀ aemeasurable_id

/-- The first marginal of the graph plan of an a.e. measurable `T` is `μ`. -/
@[simp]
theorem fst_graphPlan (hT : AEMeasurable T μ) : (graphPlan T μ).fst = μ := by
  rw [graphPlan_def, Measure.fst_map_prodMk₀ hT, Measure.map_id']

/-- The graph plan of an a.e. measurable `T` couples `μ` and the pushforward `μ.map T`. -/
theorem isCoupling_graphPlan_map (hT : AEMeasurable T μ) :
    IsCoupling (graphPlan T μ) μ (μ.map T) :=
  ⟨fst_graphPlan hT, snd_graphPlan T μ⟩

/-- **From the Monge problem to the Kantorovich problem**: the graph plan of a transport map
from `μ` to `ν` is a coupling of `μ` and `ν`. -/
theorem isCoupling_graphPlan (hT : HasLaw T ν μ) : IsCoupling (graphPlan T μ) μ ν :=
  hT.map_eq ▸ isCoupling_graphPlan_map hT.aemeasurable

/-- The graph plan of an a.e. measurable map couples `μ` and `ν` exactly when the map is a
transport map from `μ` to `ν`. The Monge problem is therefore the Kantorovich problem
restricted to the graph plans. -/
theorem isCoupling_graphPlan_iff (hT : AEMeasurable T μ) :
    IsCoupling (graphPlan T μ) μ ν ↔ HasLaw T ν μ :=
  ⟨fun h ↦ ⟨hT, by rw [← snd_graphPlan T μ, h.snd_eq]⟩, isCoupling_graphPlan⟩

/-- The identity is a transport map from `μ` to itself, so its graph plan — the diagonal plan,
carried by the diagonal of `X × X` — couples `μ` with itself. -/
theorem isCoupling_graphPlan_id (μ : Measure X) : IsCoupling (graphPlan id μ) μ μ :=
  isCoupling_graphPlan (MeasurePreserving.id μ).hasLaw

/-- A measurable equivalence is a transport map from `μ` to `μ.map e`. -/
theorem isCoupling_graphPlan_measurableEquiv (e : X ≃ᵐ Y) (μ : Measure X) :
    IsCoupling (graphPlan e μ) μ (μ.map e) :=
  isCoupling_graphPlan_map e.measurable.aemeasurable

/-- A function of the first coordinate is a.e. measurable for a graph plan as soon as it is
a.e. measurable for the source measure. -/
theorem aemeasurable_comp_fst_graphPlan (hT : AEMeasurable T μ) (hS : AEMeasurable S μ) :
    AEMeasurable (fun z : X × Y ↦ S z.1) (graphPlan T μ) := by
  have hfst : (graphPlan T μ).map Prod.fst = μ := fst_graphPlan hT
  exact AEMeasurable.comp_aemeasurable' (by rw [hfst]; exact hS) measurable_fst.aemeasurable

/-- Two maps that agree `μ`-almost everywhere have the same graph plan. -/
theorem graphPlan_congr (h : T =ᵐ[μ] S) : graphPlan T μ = graphPlan S μ :=
  Measure.map_congr <| h.mono fun _ hx ↦ Prod.ext rfl hx

section Functoriality

/-- Exchanging the coordinates of a graph plan gives the pushforward of `μ` along
`x ↦ (T x, x)`, the graph plan for the opposite convention. -/
theorem map_swap_graphPlan (hT : AEMeasurable T μ) :
    (graphPlan T μ).map Prod.swap = μ.map fun x ↦ (T x, x) := by
  rw [graphPlan_def, AEMeasurable.map_map_of_aemeasurable measurable_swap.aemeasurable
    (aemeasurable_prodMk_self hT)]
  rfl

/-- Postcomposing a transport map with a map that is a.e. measurable for the transported measure
pushes its graph plan forward in the second coordinate. Together with
`ProbabilityTheory.HasLaw.comp` this is how transport maps compose. -/
theorem map_prodMap_id_graphPlan {R : Y → Z} (hR : AEMeasurable R (μ.map T))
    (hT : AEMeasurable T μ) :
    (graphPlan T μ).map (Prod.map id R) = graphPlan (R ∘ T) μ := by
  have hsnd : (graphPlan T μ).map Prod.snd = μ.map T := snd_graphPlan T μ
  have hR' : AEMeasurable (Prod.map id R) (graphPlan T μ) :=
    measurable_fst.aemeasurable.prodMk
      (AEMeasurable.comp_aemeasurable' (by rw [hsnd]; exact hR) measurable_snd.aemeasurable)
  rw [graphPlan_def, AEMeasurable.map_map_of_aemeasurable hR' (aemeasurable_prodMk_self hT)]
  rfl

end Functoriality

section ChangeOfVariables

/-- **Change of variables along a graph plan**: integrating a cost against the graph plan of `T`
is integrating the cost of moving `x` to `T x`. -/
theorem lintegral_graphPlan (hT : AEMeasurable T μ) (hc : AEMeasurable c (graphPlan T μ)) :
    ∫⁻ z, c z ∂graphPlan T μ = ∫⁻ x, c (x, T x) ∂μ :=
  lintegral_map' hc (aemeasurable_prodMk_self hT)

end ChangeOfVariables

section Determinism

variable [MeasurableEq Y]

/-- The mass a graph plan of `T` gives to the complement of the graph of `S` is the mass of the
set where `T` and `S` differ. -/
theorem graphPlan_apply_compl_graph (hT : AEMeasurable T μ) (hS : AEMeasurable S μ) :
    graphPlan T μ {z : X × Y | ¬ z.2 = S z.1} = μ {x | ¬ T x = S x} := by
  have h : NullMeasurableSet {z : X × Y | ¬ z.2 = S z.1} (graphPlan T μ) :=
    (nullMeasurableSet_eq_fun measurable_snd.aemeasurable
      (aemeasurable_comp_fst_graphPlan hT hS)).compl
  calc graphPlan T μ {z : X × Y | ¬ z.2 = S z.1}
      = μ ((fun x ↦ (x, T x)) ⁻¹' {z : X × Y | ¬ z.2 = S z.1}) :=
        Measure.map_apply₀ (aemeasurable_prodMk_self hT) h
    _ = μ {x | ¬ T x = S x} := rfl

/-- A graph plan of `T` is carried by the graph of `S` exactly when `S` agrees with `T`
almost everywhere. -/
theorem ae_snd_eq_graphPlan_iff (hT : AEMeasurable T μ) (hS : AEMeasurable S μ) :
    (∀ᵐ z ∂graphPlan T μ, z.2 = S z.1) ↔ T =ᵐ[μ] S := by
  have h₁ : (∀ᵐ z ∂graphPlan T μ, z.2 = S z.1) ↔
      graphPlan T μ {z : X × Y | ¬ z.2 = S z.1} = 0 := ae_iff
  have h₂ : (∀ᵐ x ∂μ, T x = S x) ↔ μ {x | ¬ T x = S x} = 0 := ae_iff
  rw [h₁, graphPlan_apply_compl_graph hT hS, ← h₂]
  exact Iff.rfl

/-- A graph plan is carried by the graph of its map: almost every point of `graphPlan T μ` has
second coordinate the value of `T` at its first. -/
theorem ae_snd_eq_graphPlan (hT : AEMeasurable T μ) :
    ∀ᵐ z ∂graphPlan T μ, z.2 = T z.1 :=
  (ae_snd_eq_graphPlan_iff hT hT).2 (Filter.EventuallyEq.refl _ _)

omit [MeasurableEq Y] in
/-- A plan carried by the graph of `T` is the graph plan of `T` over its own first marginal.
This direction needs no hypothesis on `Y`. -/
theorem eq_graphPlan_of_ae_snd_eq (hT : AEMeasurable T π.fst) (h : ∀ᵐ z ∂π, z.2 = T z.1) :
    π = graphPlan T π.fst := by
  have hfst : π.map Prod.fst = π.fst := (rfl)
  have haem : AEMeasurable (fun x ↦ (x, T x)) (π.map Prod.fst) := by
    rw [hfst]; exact aemeasurable_prodMk_self hT
  have hmap : (π.map Prod.fst).map (fun x ↦ (x, T x)) = π.map fun z : X × Y ↦ (z.1, T z.1) :=
    AEMeasurable.map_map_of_aemeasurable haem measurable_fst.aemeasurable
  have hid : π = π.map fun z : X × Y ↦ (z.1, T z.1) := by
    conv_lhs => rw [← Measure.map_id' (μ := π)]
    exact Measure.map_congr <| h.mono fun z hz ↦ Prod.ext rfl hz
  calc π = π.map fun z : X × Y ↦ (z.1, T z.1) := hid
    _ = (π.map Prod.fst).map (fun x ↦ (x, T x)) := hmap.symm
    _ = graphPlan T π.fst := (rfl)

/-- **A plan is deterministic exactly when it is a graph plan**: a plan is the graph plan of `T`
over its own first marginal if and only if it is concentrated on the graph of `T`. -/
theorem eq_graphPlan_iff (hT : AEMeasurable T π.fst) :
    π = graphPlan T π.fst ↔ ∀ᵐ z ∂π, z.2 = T z.1 :=
  ⟨fun h ↦ h ▸ ae_snd_eq_graphPlan hT, eq_graphPlan_of_ae_snd_eq hT⟩

/-- **The map of a deterministic plan is unique**: two a.e. measurable maps have the same graph
plan exactly when they agree `μ`-almost everywhere. -/
theorem graphPlan_eq_graphPlan_iff (hT : AEMeasurable T μ) (hS : AEMeasurable S μ) :
    graphPlan T μ = graphPlan S μ ↔ T =ᵐ[μ] S :=
  ⟨fun h ↦ (ae_snd_eq_graphPlan_iff hT hS).1 (h ▸ ae_snd_eq_graphPlan hS), graphPlan_congr⟩

end Determinism

section Dirac

/-- An a.e. measurable map sends a Dirac measure to the Dirac measure at the image point. -/
private theorem map_dirac_of_aemeasurable {f : X → Y} {x : X}
    (hf : AEMeasurable f (Measure.dirac x)) :
    (Measure.dirac x).map f = Measure.dirac (f x) := by
  have hx : f x = hf.mk f x := by
    by_contra hne
    have hzero : Measure.dirac x {a | f a ≠ hf.mk f a} = 0 := ae_iff.mp hf.ae_eq_mk
    rw [Measure.dirac_apply_of_mem hne] at hzero
    exact one_ne_zero hzero
  calc
    (Measure.dirac x).map f = (Measure.dirac x).map (hf.mk f) :=
      Measure.map_congr hf.ae_eq_mk
    _ = Measure.dirac (hf.mk f x) := Measure.map_dirac' hf.measurable_mk x
    _ = Measure.dirac (f x) := by rw [hx]

/-- A transport map out of a Dirac measure forces the target to be the Dirac measure at its
value. So the unique coupling of `Measure.dirac x` with a non-Dirac probability measure `ν`,
namely the pushforward of `ν` along `y ↦ (x, y)`, is not a graph plan: the Monge problem out of
an atom is infeasible unless the target is an atom too. -/
theorem eq_dirac_of_hasLaw_dirac {x : X} (h : HasLaw T ν (Measure.dirac x)) :
    ν = Measure.dirac (T x) := by
  rw [← h.map_eq, map_dirac_of_aemeasurable h.aemeasurable]

/-- The graph plan of an a.e. measurable map at a Dirac measure is the Dirac measure at the
graph point. -/
@[simp]
theorem graphPlan_dirac {x : X} (hT : AEMeasurable T (Measure.dirac x)) :
    graphPlan T (Measure.dirac x) = Measure.dirac (x, T x) :=
  map_dirac_of_aemeasurable (aemeasurable_prodMk_self hT)

end Dirac

namespace Coupling

variable {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y}

/-- The graph plan of a transport map between two probability measures, bundled as an element of
`TauCeti.Coupling`. -/
def graph (hT : HasLaw T ν.toMeasure μ.toMeasure) : Coupling μ ν :=
  ⟨μ.map (aemeasurable_prodMk_self hT.aemeasurable), by
    rw [ProbabilityMeasure.toMeasure_map]
    exact isCoupling_graphPlan hT⟩

/-- The underlying measure of a bundled graph plan is the graph plan. -/
@[simp]
theorem coe_graph (hT : HasLaw T ν.toMeasure μ.toMeasure) :
    ((graph hT : ProbabilityMeasure (X × Y)) : Measure (X × Y)) = graphPlan T μ.toMeasure :=
  (rfl)

end Coupling

end TauCeti
