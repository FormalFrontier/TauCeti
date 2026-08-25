/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import TauCeti.Combinatorics.SimpleGraph.Sum
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
the corresponding reindexing of the edges, supplied by Mathlib's
`SimpleGraph.Iso.mapEdgeSet` and `SimpleGraph.edgeSetSumEquiv`.

Multiplicativity is the sharpest of the three: it says the vertices of the two summands are
integrated independently, which is exactly the statement that a graphon has no memory across
components.

## Main results

* `TauCeti.DenseGraphLimits.homDensity_eq_of_iso` — `t(·, W)` is a graph isomorphism invariant;
* `TauCeti.DenseGraphLimits.homDensity_bot` — `t(⊥, W) = 1`;
* `TauCeti.DenseGraphLimits.homDensity_sum` — `t(F₁ ⊕g F₂, W) = t(F₁, W) · t(F₂, W)`.

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

-- Mathlib's `edgeSetSumEquiv` has no application lemmas. Isolate the unavoidable reduction of its
-- `Sym2.fromRelNdrec` implementation here; the density proof below uses only these
-- characterizations.
private theorem edgeSetSumEquiv_symm_inl {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (c : G.edgeSet) :
    (((edgeSetSumEquiv (G := G) (H := H)).symm (Sum.inl c) : (G ⊕g H).edgeSet) :
        Sym2 (V ⊕ W)) = Sym2.map Sum.inl (c : Sym2 V) := by
  rcases c with ⟨c, hc⟩
  induction c using Sym2.ind with | _ a b => rfl

private theorem edgeSetSumEquiv_symm_inr {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (c : H.edgeSet) :
    (((edgeSetSumEquiv (G := G) (H := H)).symm (Sum.inr c) : (G ⊕g H).edgeSet) :
        Sym2 (V ⊕ W)) = Sym2.map Sum.inr (c : Sym2 W) := by
  rcases c with ⟨c, hc⟩
  induction c using Sym2.ind with | _ a b => rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
  {F₁ : SimpleGraph V₁} [DecidableRel F₁.Adj] {F₂ : SimpleGraph V₂} [DecidableRel F₂.Adj]

/-- **Normalization.** `t(⊥, W) = 1`; in particular `t(K₁, W) = 1` for the one-vertex graph
`⊥ : SimpleGraph (Fin 1)`. -/
@[simp]
theorem homDensity_bot (W : Graphon Ω μ) : homDensity (⊥ : SimpleGraph V₁) W = 1 := by
  rw [homDensity_def]
  calc
    _ = ∫ _ : V₁ → Ω, (1 : ℝ) ∂Measure.pi fun _ : V₁ => μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact Finset.prod_eq_one fun _ he => by simp at he
    _ = 1 := by simp

/-- **Isomorphism invariance.** A homomorphism density depends on its graph only up to isomorphism:
relabelling the vertices along `φ` permutes the coordinates of the product measure, which preserves
it, and carries the edges of `F₁` onto those of `F₂`. -/
theorem homDensity_eq_of_iso (φ : F₁ ≃g F₂) (W : Graphon Ω μ) :
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
  have hedge :
      (∏ d ∈ F₂.edgeFinset, edgeFactor W (x ∘ ⇑φ.toEquiv.symm) d) =
        ∏ c ∈ F₁.edgeFinset, edgeFactor W (x ∘ ⇑φ.toEquiv.symm) (Sym2.map φ c) := by
    rw [Finset.prod_subtype F₂.edgeFinset (fun _ ↦ SimpleGraph.mem_edgeFinset),
      Finset.prod_subtype F₁.edgeFinset (fun _ ↦ SimpleGraph.mem_edgeFinset)]
    · symm
      exact Fintype.prod_equiv φ.mapEdgeSet _ _ fun _ ↦ rfl
  rw [hedge]
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
  -- The combinatorial half, stated for an arbitrary assignment `z` on the sum: the edges of a
  -- disjoint sum are those of the two summands tagged by `Sum.inl` and `Sum.inr`, so the product
  -- over them splits, each factor read in the assignment restricted to its own summand.
  have hedge : ∀ z : V₁ ⊕ V₂ → Ω,
      (∏ d ∈ (F₁ ⊕g F₂).edgeFinset, edgeFactor W z d)
        = (∏ c ∈ F₁.edgeFinset, edgeFactor W (z ∘ Sum.inl) c)
          * ∏ c ∈ F₂.edgeFinset, edgeFactor W (z ∘ Sum.inr) c := by
    intro z
    have key : ∀ s : F₁.edgeSet ⊕ F₂.edgeSet,
        Sum.elim (fun c : F₁.edgeSet => edgeFactor W (z ∘ Sum.inl) (c : Sym2 V₁))
            (fun c : F₂.edgeSet => edgeFactor W (z ∘ Sum.inr) (c : Sym2 V₂)) s
          = edgeFactor W z ((edgeSetSumEquiv.symm s : (F₁ ⊕g F₂).edgeSet) : Sym2 (V₁ ⊕ V₂)) := by
      rintro (c | c)
      · rw [edgeSetSumEquiv_symm_inl, edgeFactor_map]
        rfl
      · rw [edgeSetSumEquiv_symm_inr, edgeFactor_map]
        rfl
    calc ∏ d ∈ (F₁ ⊕g F₂).edgeFinset, edgeFactor W z d
        = ∏ d : (F₁ ⊕g F₂).edgeSet, edgeFactor W z (d : Sym2 (V₁ ⊕ V₂)) :=
          Finset.prod_subtype _ (fun _ ↦ SimpleGraph.mem_edgeFinset) _
      _ = ∏ s : F₁.edgeSet ⊕ F₂.edgeSet,
            Sum.elim (fun c : F₁.edgeSet => edgeFactor W (z ∘ Sum.inl) (c : Sym2 V₁))
              (fun c : F₂.edgeSet => edgeFactor W (z ∘ Sum.inr) (c : Sym2 V₂)) s :=
          (Fintype.prod_equiv edgeSetSumEquiv.symm _ _ key).symm
      _ = (∏ c : F₁.edgeSet, edgeFactor W (z ∘ Sum.inl) (c : Sym2 V₁))
            * ∏ c : F₂.edgeSet, edgeFactor W (z ∘ Sum.inr) (c : Sym2 V₂) :=
          Fintype.prod_sum_type ..
      _ = _ := by
          congr 1 <;> exact (Finset.prod_subtype _ (fun _ ↦ SimpleGraph.mem_edgeFinset) _).symm
  -- The analytic half: an assignment on the sum is a pair of assignments, one per summand, so the
  -- integrand becomes a product of a function of the first and a function of the second.
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
    rw [hedge, hleft, hright]
  rw [homDensity_def, ← hmp.integral_comp' fun z : (V₁ ⊕ V₂) → Ω =>
      ∏ d ∈ (F₁ ⊕g F₂).edgeFinset, edgeFactor W z d]
  simp_rw [hsplit]
  rw [integral_prod_mul (fun y : V₁ → Ω => ∏ c ∈ F₁.edgeFinset, edgeFactor W y c)
    (fun y : V₂ → Ω => ∏ c ∈ F₂.edgeFinset, edgeFactor W y c), homDensity_def, homDensity_def]

end DenseGraphLimits

end TauCeti
