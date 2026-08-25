/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import TauCeti.Combinatorics.SimpleGraph.EdgeFinset
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The structural laws of a homomorphism density

Read as a function of its first argument, `t(·, W)` is a real-valued parameter of finite simple
graphs. This file proves the three laws that make it one:

* **isomorphism invariance** — `t(F, W)` depends on `F` only up to `≃g`;
* **normalization** — `t(F, W) = 1` when `F` has no edges, in particular on a one-vertex graph;
* **multiplicativity** — `t(F₁ ⊕g F₂, W) = t(F₁, W) · t(F₂, W)` over a disjoint sum.

Each is a change of variables in the defining integral, made along a measure-preserving map that
Mathlib already supplies: relabelling the vertices is `MeasureTheory.measurePreserving_arrowCongr'`,
and splitting the assignments on a disjoint sum of vertex sets into a pair is
`MeasureTheory.measurePreserving_sumPiEquivProdPi_symm`, after which the two halves separate by
Fubini (`MeasureTheory.integral_prod_mul`). What each change of variables has to be matched with is
the corresponding reindexing of the edges, which
`TauCeti/Combinatorics/SimpleGraph/EdgeFinset.lean` supplies.

Multiplicativity is the sharpest of the three: it says the vertices of the two summands are
integrated independently, which is exactly the statement that a graphon has no memory across
components.

## Main results

* `TauCeti.DenseGraphLimits.homDensity_congr_iso` — `t(·, W)` is a graph isomorphism invariant;
* `TauCeti.DenseGraphLimits.homDensity_bot` — `t(⊥, W) = 1`;
* `TauCeti.DenseGraphLimits.homDensity_sum` — `t(F₁ ⊕g F₂, W) = t(F₁, W) · t(F₂, W)`;
* `TauCeti.DenseGraphLimits.homDensity_eq_mul_of_iso_sum` — the same for any graph *isomorphic* to a
  disjoint sum, which is the form a graph parameter indexed by `Fin`-representatives asks for;
* `TauCeti.DenseGraphLimits.homDensity_sum_bot` — adjoining isolated vertices changes nothing.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 (`homDensity` and its basic theory,
  "multiplicativity over disjoint unions"); the three laws are the hypotheses `IsIsoInvariant`,
  `IsNormalized` and `IsMultiplicative` that Layer 8 imposes on a graph parameter.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.2 and
  §5.2.
-/

public section

noncomputable section

open MeasureTheory SimpleGraph

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
  {F₁ : SimpleGraph V₁} [DecidableRel F₁.Adj] {F₂ : SimpleGraph V₂} [DecidableRel F₂.Adj]

/-- A graph with no edges has density `1`: the integrand is the empty product. -/
theorem homDensity_eq_one_of_edgeSet_eq_empty (F : SimpleGraph V₁) [DecidableRel F.Adj]
    (W : Graphon Ω μ) (hF : F.edgeSet = ∅) : homDensity F W = 1 := by
  have h : ∀ x : V₁ → Ω, ∏ e ∈ F.edgeFinset, edgeFactor W x e = 1 := fun x =>
    Finset.prod_eq_one fun e he => by
      rw [SimpleGraph.mem_edgeFinset, hF] at he
      exact absurd he (Set.notMem_empty e)
  rw [homDensity_def]
  simp_rw [h]
  simp

/-- **Normalization.** `t(⊥, W) = 1`; in particular `t(K₁, W) = 1` for the one-vertex graph
`⊥ : SimpleGraph (Fin 1)`. -/
@[simp]
theorem homDensity_bot (W : Graphon Ω μ) : homDensity (⊥ : SimpleGraph V₁) W = 1 :=
  homDensity_eq_one_of_edgeSet_eq_empty _ W SimpleGraph.edgeSet_bot

/-- **Isomorphism invariance.** A homomorphism density depends on its graph only up to isomorphism:
relabelling the vertices along `φ` permutes the coordinates of the product measure, which preserves
it, and carries the edges of `F₁` onto those of `F₂`. -/
theorem homDensity_congr_iso (φ : F₁ ≃g F₂) (W : Graphon Ω μ) :
    homDensity F₂ W = homDensity F₁ W := by
  have hmp : MeasurePreserving (MeasurableEquiv.arrowCongr' φ.toEquiv (MeasurableEquiv.refl Ω))
      (Measure.pi fun _ : V₁ => μ) (Measure.pi fun _ : V₂ => μ) :=
    measurePreserving_arrowCongr' (fun _ => μ) (fun _ => μ) φ.toEquiv (MeasurableEquiv.refl Ω)
      fun _ => MeasurePreserving.id μ
  rw [homDensity_def, homDensity_def,
    ← hmp.integral_comp' fun y : V₂ → Ω => ∏ d ∈ F₂.edgeFinset, edgeFactor W y d]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have harrow :
      (MeasurableEquiv.arrowCongr' φ.toEquiv (MeasurableEquiv.refl Ω)) x
        = x ∘ ⇑φ.toEquiv.symm := by
    funext v
    exact Equiv.arrowCongr'_apply φ.toEquiv (Equiv.refl Ω) x v
  simp only [harrow]
  rw [prod_edgeFinset_iso φ]
  have hcomp : (x ∘ ⇑φ.toEquiv.symm) ∘ ⇑φ = x := by
    funext v
    exact congrArg x (φ.toEquiv.symm_apply_apply v)
  exact Finset.prod_congr rfl fun c _ => by rw [edgeFactor_map, hcomp]

/-- **Multiplicativity over disjoint unions.** `t(F₁ ⊕g F₂, W) = t(F₁, W) · t(F₂, W)`.

An assignment of vertices of the disjoint sum is a *pair* of assignments, one for each summand, and
the product measure on the sum of the index types is the product of the two product measures; the
edges of the sum likewise split, so the integrand is a product of a function of the first
assignment and a function of the second, and Fubini separates the two integrals. -/
@[simp]
theorem homDensity_sum (W : Graphon Ω μ) :
    homDensity (F₁ ⊕g F₂) W = homDensity F₁ W * homDensity F₂ W := by
  have hmp : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi fun _ : V₁ ⊕ V₂ => Ω).symm
      ((Measure.pi fun _ : V₁ => μ).prod (Measure.pi fun _ : V₂ => μ))
      (Measure.pi fun _ : V₁ ⊕ V₂ => μ) :=
    measurePreserving_sumPiEquivProdPi_symm fun _ : V₁ ⊕ V₂ => μ
  have hsplit : ∀ p : (V₁ → Ω) × (V₂ → Ω),
      (∏ d ∈ (F₁ ⊕g F₂).edgeFinset,
          edgeFactor W ((MeasurableEquiv.sumPiEquivProdPi fun _ : V₁ ⊕ V₂ => Ω).symm p) d)
        = (∏ c ∈ F₁.edgeFinset, edgeFactor W p.1 c)
          * ∏ c ∈ F₂.edgeFinset, edgeFactor W p.2 c := by
    intro p
    have hleft :
        ((MeasurableEquiv.sumPiEquivProdPi fun _ : V₁ ⊕ V₂ => Ω).symm p) ∘ Sum.inl = p.1 := by
      funext v
      rw [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]
    have hright :
        ((MeasurableEquiv.sumPiEquivProdPi fun _ : V₁ ⊕ V₂ => Ω).symm p) ∘ Sum.inr = p.2 := by
      funext v
      rw [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]
    rw [prod_edgeFinset_sum]
    congr 1
    · exact Finset.prod_congr rfl fun c _ => by rw [edgeFactor_map, hleft]
    · exact Finset.prod_congr rfl fun c _ => by rw [edgeFactor_map, hright]
  rw [homDensity_def, ← hmp.integral_comp' fun z : (V₁ ⊕ V₂) → Ω =>
      ∏ d ∈ (F₁ ⊕g F₂).edgeFinset, edgeFactor W z d]
  simp_rw [hsplit]
  rw [integral_prod_mul (fun y : V₁ → Ω => ∏ c ∈ F₁.edgeFinset, edgeFactor W y c)
    (fun y : V₂ → Ω => ∏ c ∈ F₂.edgeFinset, edgeFactor W y c), homDensity_def, homDensity_def]

/-- Multiplicativity in the form a graph parameter carried on `Fin`-representatives asks for: any
graph *isomorphic* to a disjoint sum has the product density.  Combining
`TauCeti.DenseGraphLimits.homDensity_sum` with isomorphism invariance removes the need for the
vertex type to be a literal `⊕`. -/
theorem homDensity_eq_mul_of_iso_sum {V : Type*} [Fintype V] {F : SimpleGraph V}
    [DecidableRel F.Adj] (φ : F ≃g F₁ ⊕g F₂) (W : Graphon Ω μ) :
    homDensity F W = homDensity F₁ W * homDensity F₂ W := by
  rw [← homDensity_congr_iso φ, homDensity_sum]

/-- **The added-vertex telescope.** Adjoining isolated vertices leaves a density unchanged — the
combination of multiplicativity with normalization that a level-by-level count of labelled graphs
runs on. -/
theorem homDensity_sum_bot (W : Graphon Ω μ) :
    homDensity (F₁ ⊕g (⊥ : SimpleGraph V₂)) W = homDensity F₁ W := by
  rw [homDensity_sum, homDensity_bot, mul_one]

end DenseGraphLimits

end TauCeti
