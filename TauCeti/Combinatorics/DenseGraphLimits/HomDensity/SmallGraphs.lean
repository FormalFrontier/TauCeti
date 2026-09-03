/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Homomorphism densities of the smallest graphs

The two homomorphism densities that the rest of the theory quotes by name:

```text
t(K₂, W) = ∫∫ W(x, y)                              the edge density
t(K₃, W) = ∫∫∫ W(x, y) W(x, z) W(y, z)             the triangle density
```

Each is given twice: once as an integral against a product measure, and once in the iterated form
above.  The two are related by `integral_prod`, which needs the integrand to be integrable, so those
integrability lemmas are part of the public interface rather than hidden inside a proof.  They are
proved for an arbitrary graph by transporting `integrable_homDensity_integrand` along the same
equivalence that transports the density, so no measurability or boundedness argument is repeated.

**The transport is separated from the graph.**  `homDensity` integrates over the function space
`Fin n → Ω`, and moving to `Ω × ⋯ × Ω` is independent of which graph is being counted.  That step is
therefore proved once, for an arbitrary graph, as `homDensity_fin_two` and `homDensity_fin_three`;
each concrete value below is then just its edge set (computed by `decide`) substituted into the
general statement.  A further entry in this catalogue — a single edge on three vertices, a path, the
empty graph — costs only that substitution.

**Where the transports come from.**  For two vertices it is Mathlib's `MeasurableEquiv.finTwoArrow`
with `measurePreserving_finTwoArrow`.  Mathlib supplies no `(Fin 3 → Ω) ≃ᵐ Ω × Ω × Ω`, so the
three-vertex one is composed here as `finThreeArrow`, out of `MeasurableEquiv.piFinSuccAbove` and
`finTwoArrow`, with measure preservation assembled from the corresponding two Mathlib lemmas.  It
sends `x` to `(x 0, x 1, x 2)` definitionally; `finThreeArrow_apply` records that by `rfl` so the
coordinate matching in the proofs is an explicit rewrite rather than a silent unfolding.

## Main results

* `homDensity_fin_two`, `homDensity_fin_three` — the graph-independent transports;
* `homDensity_top_fin_two` and `homDensity_top_fin_two_eq_integral_integral` — the edge density;
* `homDensity_top_fin_three` and `homDensity_top_fin_three_eq_integral_integral_integral` — the
  triangle density;
* `integrable_prod_edgeFactor_fin_two`, `integrable_prod_edgeFactor_fin_three` — integrability of
  the transported integrand, again for an arbitrary graph;
* `integrable_edge_integrand`, `integrable_triangle_integrand` — the same for the two expanded
  integrands, so a consumer of either iterated form has the hypothesis `integral_prod` needs.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — the explicit small-graph
  integrals, and the Layer 1 acceptance criteria "a one-edge graph" and "triangle density".
  Disjoint-union multiplicativity, finite-graph compatibility, and the counting lemmas are separate
  targets and are not built here.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.2.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The transport from three independent coordinates to a triple product.  Mathlib has the
two-coordinate version (`MeasurableEquiv.finTwoArrow`) but not this one. -/
private def finThreeArrow (Ω : Type*) [MeasurableSpace Ω] : (Fin 3 → Ω) ≃ᵐ Ω × Ω × Ω :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Ω) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Ω) MeasurableEquiv.finTwoArrow)

/-- `finThreeArrow` reads off the three coordinates.  This holds by `rfl`, and is stated so that the
proofs below rewrite with it instead of relying on the definitional unfolding of
`Fin.succAbove`. -/
@[simp]
private theorem finThreeArrow_apply (x : Fin 3 → Ω) : finThreeArrow Ω x = (x 0, x 1, x 2) := (rfl)

private theorem measurePreserving_finThreeArrow (μ : Measure Ω) [SigmaFinite μ] :
    MeasurePreserving (finThreeArrow Ω) (Measure.pi fun _ : Fin 3 => μ) (μ.prod (μ.prod μ)) :=
  ((MeasurePreserving.id μ).prod (measurePreserving_finTwoArrow μ)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0)

/-- **The two-vertex transport.**  For any graph on `Fin 2`, the homomorphism density is an integral
over `Ω × Ω`.  This is independent of the graph; the concrete values below only substitute an edge
set into it. -/
theorem homDensity_fin_two (F : SimpleGraph (Fin 2)) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    homDensity F W
      = ∫ p : Ω × Ω, ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1, p.2] e ∂(μ.prod μ) := by
  have key : ∀ x : Fin 2 → Ω,
      ∏ e ∈ F.edgeFinset, edgeFactor W x e = ∏ e ∈ F.edgeFinset, edgeFactor W ![x 0, x 1] e := by
    intro x
    have hx : ![x 0, x 1] = x := FinVec.etaExpand_eq x
    rw [hx]
  rw [homDensity_def, ← (measurePreserving_finTwoArrow μ).integral_comp
    MeasurableEquiv.finTwoArrow.measurableEmbedding
    (fun p : Ω × Ω => ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1, p.2] e)]
  simp only [MeasurableEquiv.finTwoArrow_apply]
  exact integral_congr_ae (ae_of_all _ fun x => key x)

/-- **The three-vertex transport.**  For any graph on `Fin 3`, the homomorphism density is an
integral over `Ω × Ω × Ω`. -/
theorem homDensity_fin_three (F : SimpleGraph (Fin 3)) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    homDensity F W
      = ∫ p : Ω × Ω × Ω, ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1, p.2.1, p.2.2] e
          ∂(μ.prod (μ.prod μ)) := by
  have key : ∀ x : Fin 3 → Ω,
      ∏ e ∈ F.edgeFinset, edgeFactor W x e
        = ∏ e ∈ F.edgeFinset, edgeFactor W ![x 0, x 1, x 2] e := by
    intro x
    have hx : ![x 0, x 1, x 2] = x := FinVec.etaExpand_eq x
    rw [hx]
  rw [homDensity_def, ← (measurePreserving_finThreeArrow μ).integral_comp
    (finThreeArrow Ω).measurableEmbedding
    (fun p : Ω × Ω × Ω => ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1, p.2.1, p.2.2] e)]
  simp only [finThreeArrow_apply]
  exact integral_congr_ae (ae_of_all _ fun x => key x)

/-- **Transported integrability, two vertices.**  For any graph on `Fin 2`, the transported
integrand is integrable — obtained from `integrable_homDensity_integrand` along the same
equivalence that transports the density, so no measurability or bound is re-argued. -/
theorem integrable_prod_edgeFactor_fin_two (F : SimpleGraph (Fin 2)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω => ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1, p.2] e) (μ.prod μ) := by
  refine ((measurePreserving_finTwoArrow μ).integrable_comp_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding).mp ?_
  refine (integrable_homDensity_integrand F W).congr (ae_of_all _ fun x => ?_)
  simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply]
  have hx : ![x 0, x 1] = x := FinVec.etaExpand_eq x
  rw [hx]

/-- **Transported integrability, three vertices.** -/
theorem integrable_prod_edgeFactor_fin_three (F : SimpleGraph (Fin 3)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω × Ω => ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1, p.2.1, p.2.2] e)
      (μ.prod (μ.prod μ)) := by
  refine ((measurePreserving_finThreeArrow μ).integrable_comp_emb
    (finThreeArrow Ω).measurableEmbedding).mp ?_
  refine (integrable_homDensity_integrand F W).congr (ae_of_all _ fun x => ?_)
  simp only [Function.comp_apply, finThreeArrow_apply]
  have hx : ![x 0, x 1, x 2] = x := FinVec.etaExpand_eq x
  rw [hx]

/-- The edge factor product of `K₂`, expanded.  Shared by the density value and its
integrability. -/
private theorem prod_edgeFactor_top_fin_two (W : Graphon Ω μ) (p : Ω × Ω) :
    ∏ e ∈ (⊤ : SimpleGraph (Fin 2)).edgeFinset, edgeFactor W ![p.1, p.2] e = W p.1 p.2 := by
  have hedge : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by decide
  rw [hedge, Finset.prod_singleton, edgeFactor_mk]
  simp

/-- The edge factor product of `K₃`, expanded.  Shared by the density value and its
integrability. -/
private theorem prod_edgeFactor_top_fin_three (W : Graphon Ω μ) (p : Ω × Ω × Ω) :
    ∏ e ∈ (⊤ : SimpleGraph (Fin 3)).edgeFinset, edgeFactor W ![p.1, p.2.1, p.2.2] e
      = W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2 := by
  have hedge : (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by decide
  rw [hedge, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [edgeFactor_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The edge integrand is integrable, by transport from `integrable_prod_edgeFactor_fin_two`. -/
theorem integrable_edge_integrand (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω => W p.1 p.2) (μ.prod μ) :=
  (integrable_prod_edgeFactor_fin_two ⊤ W).congr
    (ae_of_all _ fun p => prod_edgeFactor_top_fin_two W p)

/-- The triangle integrand is integrable, by transport from
`integrable_prod_edgeFactor_fin_three`. -/
theorem integrable_triangle_integrand (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω × Ω => W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2)
      (μ.prod (μ.prod μ)) :=
  (integrable_prod_edgeFactor_fin_three ⊤ W).congr
    (ae_of_all _ fun p => prod_edgeFactor_top_fin_three W p)

/-- **The edge density.**  The homomorphism density of the one-edge graph `K₂` is the integral of
the graphon over the whole square. -/
theorem homDensity_top_fin_two (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 2)) W = ∫ p : Ω × Ω, W p.1 p.2 ∂(μ.prod μ) := by
  rw [homDensity_fin_two]
  exact integral_congr_ae (ae_of_all _ fun p => prod_edgeFactor_top_fin_two W p)

/-- The edge density as an iterated integral. -/
theorem homDensity_top_fin_two_eq_integral_integral (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 2)) W = ∫ x, ∫ y, W x y ∂μ ∂μ := by
  rw [homDensity_top_fin_two, integral_prod _ (integrable_edge_integrand W)]

/-- **The triangle density.**  The homomorphism density of `K₃` is the integral of the product of
the graphon over the three edges of a triple of points. -/
theorem homDensity_top_fin_three (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W
      = ∫ p : Ω × Ω × Ω, W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2 ∂(μ.prod (μ.prod μ)) := by
  rw [homDensity_fin_three]
  exact integral_congr_ae (ae_of_all _ fun p => prod_edgeFactor_top_fin_three W p)

/-- The triangle density as an iterated integral. -/
theorem homDensity_top_fin_three_eq_integral_integral_integral (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W = ∫ x, ∫ y, ∫ z, W x y * W x z * W y z ∂μ ∂μ ∂μ := by
  rw [homDensity_top_fin_three, integral_prod _ (integrable_triangle_integrand W)]
  refine integral_congr_ae ?_
  filter_upwards [(integrable_triangle_integrand W).prod_right_ae] with x hx
  exact integral_prod _ hx

end DenseGraphLimits

end TauCeti
