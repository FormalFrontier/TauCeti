/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import TauCeti.MeasureTheory.OptimalTransport.GraphPlan

/-!
# The transport cost of two measures

Given a cost `c : X × Y → ℝ≥0∞`, the *transport cost* of `μ` and `ν` is the infimum of
`∫⁻ z, c z ∂π` over the couplings `π` of `μ` and `ν`. This is the value of the primal
Kantorovich problem, and it is the root definition of optimal transport: every later notion —
Wasserstein distance, Kantorovich duality, transport maps — is a statement about this number or
about the plans that attain it.

The definition is made for arbitrary measures on arbitrary measurable spaces, with an
extended-nonnegative cost integrated by `lintegral`. Nothing is assumed about topology,
finiteness, or normalisation, and no compactness is built in. An empty feasible set — for
instance measures of different total mass — gives the value `∞`, as does a cost that is too
large on every plan; the two are separated by
`TauCeti.exists_isCoupling_of_transportCost_ne_top`.

## Main definitions

* `TauCeti.transportCost c μ ν` — the infimum of `∫⁻ z, c z ∂π` over the couplings `π` of `μ`
  and `ν`;
* `TauCeti.IsOptimalCoupling c π μ ν` — the predicate cutting out the optimal plans: `π` is a
  coupling of `μ` and `ν` whose cost is `transportCost c μ ν`.

## Main statements

* `TauCeti.transportCost_le_lintegral` and `TauCeti.le_transportCost` — the two halves of the
  universal property of the infimum, with `TauCeti.transportCost_lt_iff` its order-theoretic
  restatement;
* `TauCeti.transportCost_mono`, `TauCeti.transportCost_congr`, `TauCeti.transportCost_const`,
  `TauCeti.transportCost_const_mul` and `TauCeti.transportCost_add_split` — monotonicity in the
  cost, invariance under a change of cost that is a.e. invisible to every feasible plan, the
  value of a constant cost, positive scaling, and the effect of adding integrable terms
  depending on one variable each;
* `TauCeti.transportCost_comp_swap`, `TauCeti.transportCost_comm` and
  `TauCeti.transportCost_comp_prodMap` — functoriality: exchanging the two factors, symmetry for
  a symmetric cost, and invariance under measurable equivalences of the two factors;
* `TauCeti.transportCost_dirac_left`, `TauCeti.transportCost_dirac_right` and
  `TauCeti.transportCost_dirac_dirac` — the exact value when either marginal is a Dirac
  measure, where the plan is unique;
* `TauCeti.isOptimalCoupling_iff` — optimality is minimality among feasible plans, so it does
  not depend on the value `transportCost c μ ν` being finite, with the left and right Dirac
  lemmas giving the first families of optimal plans;
* `TauCeti.transportCost_le_lintegral_of_hasLaw` — the Monge-to-Kantorovich inequality: the
  transport cost of `μ` and `ν` is at most the cost `∫⁻ x, c (x, T x) ∂μ` of any transport map
  `T` from `μ` to `ν`, with `TauCeti.isOptimalCoupling_graphPlan_iff` its equality case.

## Implementation notes

The infimum is written as an iterated `⨅` over plans and over proofs of `TauCeti.IsCoupling`,
so that it is `∞` on an empty feasible set with no case split, and so that
`TauCeti.transportCost_le_lintegral` is `iInf₂_le`.

Invariance of the transport cost under a change of the cost function needs the two costs to
agree a.e. for *every* feasible plan, not merely `μ.prod ν`-a.e.: a coupling can be singular
with respect to the product measure — the diagonal plan of `μ` with itself on a diffuse `μ` is —
so a `μ.prod ν`-null set can carry all the mass of some competitor. This is why
`TauCeti.transportCost_congr` quantifies over plans.

Measurability of the cost is assumed only where it is used, namely in the theorems that move an
integral along a pushforward (`TauCeti.transportCost_comp_swap`,
`TauCeti.transportCost_comp_prodMap` and the Dirac formulas). The order-theoretic API needs
none.

The Monge-to-Kantorovich inequality is a statement about the transport cost, so it is stated
here; the graph plan that witnesses it and the change of variables it uses come from
`TauCeti/MeasureTheory/OptimalTransport/GraphPlan.lean`, which is below this module. Its
inequality half needs no measurability of the cost at all, since only one half of the change of
variables, `MeasureTheory.lintegral_map_le`, is used.

This supplies the nonnegative-cost interface from Layer 1, item 1 of the optimal-transport
roadmap. The parallel signed `EReal` interface for costs bounded below by an integrable split
function is a separate definition family and is not part of this module.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §1.1.1, where "Kantorovich's mass transportation problem consists in minimizing the linear
  functional `π ↦ ∫ c dπ`" over the transference plans. Villani takes `μ` and `ν` to be
  probability measures and `c` nonnegative measurable; `TauCeti.transportCost` drops the
  normalisation and reads `c` into `ℝ≥0∞`, so an infeasible pair simply gets the value `∞`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

universe u v w

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']
  {c c' : X × Y → ℝ≥0∞} {π σ : Measure (X × Y)} {μ : Measure X} {ν : Measure Y} {T : X → Y}
  {a : ℝ≥0∞}

/-- The transport cost of `μ` and `ν` for the cost function `c`: the infimum of `∫⁻ z, c z ∂π`
over the couplings `π` of `μ` and `ν`. It is `∞` when `μ` and `ν` have no coupling at all. -/
def transportCost (c : X × Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y) : ℝ≥0∞ :=
  ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), ∫⁻ z, c z ∂π

/-- Every coupling bounds the transport cost from above. -/
theorem transportCost_le_lintegral (hπ : IsCoupling π μ ν) (c : X × Y → ℝ≥0∞) :
    transportCost c μ ν ≤ ∫⁻ z, c z ∂π :=
  iInf₂_le π hπ

/-- A bound valid on every coupling bounds the transport cost from below. -/
theorem le_transportCost (h : ∀ π, IsCoupling π μ ν → a ≤ ∫⁻ z, c z ∂π) :
    a ≤ transportCost c μ ν :=
  le_iInf₂ h

/-- The transport cost is below a threshold exactly when some coupling is. -/
theorem transportCost_lt_iff :
    transportCost c μ ν < a ↔ ∃ π, IsCoupling π μ ν ∧ ∫⁻ z, c z ∂π < a := by
  simp only [transportCost, iInf_lt_iff, exists_prop]

/-- Measures with no coupling — for instance, by `TauCeti.exists_isCoupling_iff`, a finite
measure and a measure of a different total mass — have transport cost `∞`. -/
theorem transportCost_eq_top_of_not_exists_isCoupling (h : ¬ ∃ π, IsCoupling π μ ν)
    (c : X × Y → ℝ≥0∞) : transportCost c μ ν = ⊤ :=
  eq_top_iff.2 <| le_transportCost fun π hπ ↦ absurd ⟨π, hπ⟩ h

/-- A finite measure and a measure of a different total mass have transport cost `∞`. -/
theorem transportCost_eq_top_of_measure_univ_ne [IsFiniteMeasure μ] (h : μ univ ≠ ν univ)
    (c : X × Y → ℝ≥0∞) : transportCost c μ ν = ⊤ :=
  transportCost_eq_top_of_not_exists_isCoupling (fun hex ↦ h (exists_isCoupling_iff.1 hex)) c

/-- A finite transport cost is witnessed by a coupling. The converse fails: a coupling of
infinite cost leaves the transport cost `∞`, which is why this is not stated as an
`iff` with `TauCeti.transportCost_eq_top_of_not_exists_isCoupling`. -/
theorem exists_isCoupling_of_transportCost_ne_top (h : transportCost c μ ν ≠ ⊤) :
    ∃ π, IsCoupling π μ ν := by
  obtain ⟨π, hπ, -⟩ := transportCost_lt_iff.1 h.lt_top
  exact ⟨π, hπ⟩

/-- The transport cost is monotone in the cost function. -/
@[gcongr]
theorem transportCost_mono (h : c ≤ c') : transportCost c μ ν ≤ transportCost c' μ ν :=
  iInf₂_mono fun _ _ ↦ lintegral_mono h

/-- Two costs that agree almost everywhere for every feasible plan have the same transport cost.
Agreeing `μ.prod ν`-almost everywhere is *not* enough: a coupling may be singular with respect
to the product measure. -/
theorem transportCost_congr (h : ∀ π, IsCoupling π μ ν → c =ᵐ[π] c') :
    transportCost c μ ν = transportCost c' μ ν :=
  le_antisymm (iInf₂_mono fun π hπ ↦ (lintegral_congr_ae (h π hπ)).le)
    (iInf₂_mono fun π hπ ↦ (lintegral_congr_ae (h π hπ)).ge)

section Const

/-- A constant cost has transport cost that constant times the total mass, as soon as some
coupling exists. -/
theorem transportCost_const (h : ∃ π, IsCoupling π μ ν) (a : ℝ≥0∞) :
    transportCost (fun _ ↦ a) μ ν = a * μ univ := by
  obtain ⟨π₀, hπ₀⟩ := h
  refine le_antisymm ?_ (le_transportCost fun π hπ ↦ ?_)
  · calc transportCost (fun _ ↦ a) μ ν ≤ ∫⁻ _, a ∂π₀ := transportCost_le_lintegral hπ₀ _
      _ = a * μ univ := by rw [lintegral_const, hπ₀.measure_univ_left]
  · rw [lintegral_const, hπ.measure_univ_left]

/-- The zero cost has zero transport cost, as soon as some coupling exists. Feasibility is
needed: with no coupling the value is `∞`. This is also why `TauCeti.transportCost_const_mul`
excludes the scalar `0`, for which its right-hand side would read `0 * ∞ = 0`. -/
theorem transportCost_zero (h : ∃ π, IsCoupling π μ ν) :
    transportCost (fun _ ↦ (0 : ℝ≥0∞)) μ ν = 0 := by
  rw [transportCost_const h, zero_mul]

/-- Scaling the cost by a nonzero finite constant scales the transport cost. -/
theorem transportCost_const_mul (ha₀ : a ≠ 0) (ha : a ≠ ⊤) :
    transportCost (fun z ↦ a * c z) μ ν = a * transportCost c μ ν := by
  simp only [transportCost, lintegral_const_mul' _ _ ha, ← ENNReal.mul_iInf_of_ne ha₀ ha]

end Const

section Split

variable {f : X → ℝ≥0∞} {g : Y → ℝ≥0∞}

/-- The cost of a fixed plan splits off the terms depending on one variable each: those
contribute the two marginal integrals, which do not depend on the plan. -/
theorem IsCoupling.lintegral_add_split (hπ : IsCoupling π μ ν) (hf : Measurable f)
    (hg : Measurable g) (c : X × Y → ℝ≥0∞) :
    ∫⁻ z, (c z + f z.1 + g z.2) ∂π = ∫⁻ z, c z ∂π + ∫⁻ x, f x ∂μ + ∫⁻ y, g y ∂ν := by
  have hf' : Measurable fun z : X × Y ↦ f z.1 := hf.comp measurable_fst
  have hg' : Measurable fun z : X × Y ↦ g z.2 := hg.comp measurable_snd
  have hfst : ∫⁻ z, f z.1 ∂π = ∫⁻ x, f x ∂μ := by
    rw [← hπ.fst_eq]
    exact (lintegral_map hf measurable_fst).symm
  have hsnd : ∫⁻ z, g z.2 ∂π = ∫⁻ y, g y ∂ν := by
    rw [← hπ.snd_eq]
    exact (lintegral_map hg measurable_snd).symm
  rw [lintegral_add_right _ hg', lintegral_add_right _ hf', hfst, hsnd]

/-- Adding to the cost a term in the first variable and a term in the second shifts the
transport cost by the two marginal integrals. Both sides are `∞` when there is no coupling, so
no feasibility hypothesis is needed. -/
theorem transportCost_add_split (hf : Measurable f) (hg : Measurable g) :
    transportCost (fun z ↦ c z + f z.1 + g z.2) μ ν
      = transportCost c μ ν + ∫⁻ x, f x ∂μ + ∫⁻ y, g y ∂ν := by
  simp only [transportCost, ENNReal.iInf_add]
  exact iInf_congr fun π ↦ iInf_congr fun hπ ↦ hπ.lintegral_add_split hf hg c

end Split

section Functoriality

/-- The transport cost is unchanged by exchanging the two factors, the cost being transported
along the same exchange. -/
theorem transportCost_comp_swap (hc : Measurable c) (μ : Measure X) (ν : Measure Y) :
    transportCost (fun z ↦ c z.swap) ν μ = transportCost c μ ν := by
  have hcs : Measurable fun z : Y × X ↦ c z.swap := hc.comp measurable_swap
  refine le_antisymm (le_transportCost fun π hπ ↦ ?_) (le_transportCost fun σ hσ ↦ ?_)
  · calc transportCost (fun z ↦ c z.swap) ν μ ≤ ∫⁻ w, c w.swap ∂π.map Prod.swap :=
        transportCost_le_lintegral hπ.swap _
      _ = ∫⁻ z, c z ∂π := by
        rw [lintegral_map hcs measurable_swap]
        simp
  · calc transportCost c μ ν ≤ ∫⁻ z, c z ∂σ.map Prod.swap :=
        transportCost_le_lintegral hσ.swap _
      _ = ∫⁻ w, c w.swap ∂σ := lintegral_map hc measurable_swap

/-- A symmetric cost gives a symmetric transport cost. -/
theorem transportCost_comm {c : X × X → ℝ≥0∞} (hc : Measurable c)
    (hsymm : ∀ x y, c (x, y) = c (y, x)) (μ ν : Measure X) :
    transportCost c μ ν = transportCost c ν μ := by
  have h : (fun z : X × X ↦ c z.swap) = c := funext fun z ↦ hsymm z.2 z.1
  rw [← transportCost_comp_swap hc μ ν, h]

/-- The transport cost is invariant under measurable equivalences of the two factors: pushing
the marginals forward and transporting the cost back gives the same value. -/
theorem transportCost_comp_prodMap (e : X ≃ᵐ X') (f : Y ≃ᵐ Y') {c : X' × Y' → ℝ≥0∞}
    (hc : Measurable c) (μ : Measure X) (ν : Measure Y) :
    transportCost (fun z ↦ c (e z.1, f z.2)) μ ν = transportCost c (μ.map e) (ν.map f) := by
  have key (π : Measure (X × Y)) :
      ∫⁻ w, c w ∂π.map (Prod.map e f) = ∫⁻ z, c (e z.1, f z.2) ∂π :=
    lintegral_map hc (e.measurable.prodMap f.measurable)
  refine le_antisymm (le_transportCost fun σ hσ ↦ ?_) (le_transportCost fun π hπ ↦ ?_)
  · have hmap : (σ.map (Prod.map e.symm f.symm)).map (Prod.map e f) = σ :=
      MeasurableEquiv.map_map_symm (ν := σ) (e.prodCongr f)
    have hπ : IsCoupling (σ.map (Prod.map e.symm f.symm)) μ ν :=
      (isCoupling_map_prodMap_iff e f).1 (by rw [hmap]; exact hσ)
    calc transportCost (fun z ↦ c (e z.1, f z.2)) μ ν
        ≤ ∫⁻ z, c (e z.1, f z.2) ∂σ.map (Prod.map e.symm f.symm) :=
          transportCost_le_lintegral hπ _
      _ = ∫⁻ w, c w ∂σ := by rw [← key, hmap]
  · calc transportCost c (μ.map e) (ν.map f) ≤ ∫⁻ w, c w ∂π.map (Prod.map e f) :=
        transportCost_le_lintegral (hπ.map e.measurable f.measurable) _
      _ = ∫⁻ z, c (e z.1, f z.2) ∂π := key π

end Functoriality

section Dirac

/-- A Dirac source has exactly one coupling with each probability target, so its transport cost
is an integral against the target. -/
theorem transportCost_dirac_left [IsProbabilityMeasure ν] (hc : Measurable c) (x : X) :
    transportCost c (Measure.dirac x) ν = ∫⁻ y, c (x, y) ∂ν := by
  refine le_antisymm ?_ (le_transportCost fun π hπ ↦ ?_)
  · calc transportCost c (Measure.dirac x) ν ≤ ∫⁻ z, c z ∂ν.map (Prod.mk x) :=
        transportCost_le_lintegral (isCoupling_map_prodMk x ν) _
      _ = ∫⁻ y, c (x, y) ∂ν := lintegral_map hc measurable_prodMk_left
  · rw [hπ.eq_map_prodMk, lintegral_map hc measurable_prodMk_left]

/-- A Dirac target has exactly one coupling with each probability source, so its transport cost
is an integral against the source. -/
theorem transportCost_dirac_right [IsProbabilityMeasure μ] (hc : Measurable c) (y : Y) :
    transportCost c μ (Measure.dirac y) = ∫⁻ x, c (x, y) ∂μ := by
  rw [← transportCost_comp_swap hc μ (Measure.dirac y)]
  exact transportCost_dirac_left (hc.comp measurable_swap) y

/-- Two Dirac measures have exactly one coupling, so their transport cost is the value of the
cost at the pair. -/
theorem transportCost_dirac_dirac (hc : Measurable c) (x : X) (y : Y) :
    transportCost c (Measure.dirac x) (Measure.dirac y) = c (x, y) := by
  have hcx : Measurable fun y : Y ↦ c (x, y) := hc.comp measurable_prodMk_left
  rw [transportCost_dirac_left hc x, lintegral_dirac' _ hcx]

end Dirac

/-- `IsOptimalCoupling c π μ ν` says that the plan `π` solves the primal transport problem: it
couples `μ` and `ν`, and its cost is the transport cost of the pair. The optimal plans are the
set cut out by this predicate. -/
structure IsOptimalCoupling (c : X × Y → ℝ≥0∞) (π : Measure (X × Y)) (μ : Measure X)
    (ν : Measure Y) : Prop extends IsCoupling π μ ν where
  /-- An optimal coupling attains the transport cost. -/
  lintegral_eq : ∫⁻ z, c z ∂π = transportCost c μ ν

namespace IsOptimalCoupling

/-- An optimal coupling costs no more than any other coupling of the same pair. -/
theorem lintegral_le (h : IsOptimalCoupling c π μ ν) (hσ : IsCoupling σ μ ν) :
    ∫⁻ z, c z ∂π ≤ ∫⁻ z, c z ∂σ :=
  h.lintegral_eq.trans_le (transportCost_le_lintegral hσ c)

/-- Pushing an optimal coupling forward along measurable equivalences gives an optimal coupling
for the pushed-forward marginals and the transported cost. -/
protected theorem map (e : X ≃ᵐ X') (f : Y ≃ᵐ Y') {c : X' × Y' → ℝ≥0∞}
    (hc : Measurable c) (h : IsOptimalCoupling (fun z ↦ c (e z.1, f z.2)) π μ ν) :
    IsOptimalCoupling c (π.map (Prod.map e f)) (μ.map e) (ν.map f) where
  toIsCoupling := h.toIsCoupling.map e.measurable f.measurable
  lintegral_eq := by
    rw [lintegral_map hc (e.measurable.prodMap f.measurable),
      ← transportCost_comp_prodMap e f hc μ ν]
    exact h.lintegral_eq

/-- Exchanging the two coordinates of an optimal coupling gives an optimal coupling for the
exchanged cost. -/
protected theorem swap (hc : Measurable c) (h : IsOptimalCoupling c π μ ν) :
    IsOptimalCoupling (fun z ↦ c z.swap) (π.map Prod.swap) ν μ where
  toIsCoupling := h.toIsCoupling.swap
  lintegral_eq := by
    have hcs : Measurable fun z : Y × X ↦ c z.swap := hc.comp measurable_swap
    rw [lintegral_map hcs measurable_swap, transportCost_comp_swap hc μ ν]
    simpa using h.lintegral_eq

end IsOptimalCoupling

/-- Optimality is minimality among the feasible plans. This form of the definition avoids the
value `transportCost c μ ν`, so it is the one to check when that value may be `∞`. -/
theorem isOptimalCoupling_iff :
    IsOptimalCoupling c π μ ν ↔
      IsCoupling π μ ν ∧ ∀ σ, IsCoupling σ μ ν → ∫⁻ z, c z ∂π ≤ ∫⁻ z, c z ∂σ :=
  ⟨fun h ↦ ⟨h.toIsCoupling, fun _ hσ ↦ h.lintegral_le hσ⟩, fun ⟨hπ, h⟩ ↦
    ⟨hπ, le_antisymm (le_transportCost h) (transportCost_le_lintegral hπ c)⟩⟩

/-- Every coupling out of a Dirac measure is optimal, because there is only one. -/
theorem IsCoupling.isOptimalCoupling_dirac_left [IsProbabilityMeasure ν] (hc : Measurable c)
    {x : X} (hπ : IsCoupling π (Measure.dirac x) ν) :
    IsOptimalCoupling c π (Measure.dirac x) ν where
  toIsCoupling := hπ
  lintegral_eq := by
    rw [hπ.eq_map_prodMk, lintegral_map hc measurable_prodMk_left, transportCost_dirac_left hc]

/-- Every coupling into a Dirac measure is optimal, because there is only one. -/
theorem IsCoupling.isOptimalCoupling_dirac_right [IsProbabilityMeasure μ] (hc : Measurable c)
    {y : Y} (hπ : IsCoupling π μ (Measure.dirac y)) :
    IsOptimalCoupling c π μ (Measure.dirac y) := by
  have hπ' : IsOptimalCoupling (fun z : Y × X ↦ c z.swap) (π.map Prod.swap)
      (Measure.dirac y) μ :=
    hπ.swap.isOptimalCoupling_dirac_left (hc.comp measurable_swap)
  have hπ'' := hπ'.swap (hc.comp measurable_swap)
  have hmap : (π.map Prod.swap).map Prod.swap = π :=
    MeasurableEquiv.map_map_symm (ν := π) MeasurableEquiv.prodComm
  rw [hmap] at hπ''
  simpa [Function.comp_def] using hπ''

section Monge

/-- **The Monge problem dominates the Kantorovich problem**: the transport cost of `μ` and `ν`
is at most the cost of any transport map from `μ` to `ν`, that is, of any map whose graph plan
`TauCeti.graphPlan` is a coupling of the two. Only one half of the change of variables is
needed, `MeasureTheory.lintegral_map_le`, so the cost needs no measurability. -/
theorem transportCost_le_lintegral_of_hasLaw (hT : HasLaw T ν μ) (c : X × Y → ℝ≥0∞) :
    transportCost c μ ν ≤ ∫⁻ x, c (x, T x) ∂μ := by
  refine (transportCost_le_lintegral (isCoupling_graphPlan hT) c).trans ?_
  rw [graphPlan_def]
  exact lintegral_map_le _ _

/-- The graph plan of a transport map is an optimal plan exactly when the transport cost equals
the cost of the map: the equality case of `TauCeti.transportCost_le_lintegral_of_hasLaw`. -/
theorem isOptimalCoupling_graphPlan_iff (hT : HasLaw T ν μ)
    (hc : AEMeasurable c (graphPlan T μ)) :
    IsOptimalCoupling c (graphPlan T μ) μ ν ↔ transportCost c μ ν = ∫⁻ x, c (x, T x) ∂μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨isCoupling_graphPlan hT, ?_⟩⟩
  · rw [← h.lintegral_eq, lintegral_graphPlan hT.aemeasurable hc]
  · rw [lintegral_graphPlan hT.aemeasurable hc, h]

end Monge

end TauCeti
