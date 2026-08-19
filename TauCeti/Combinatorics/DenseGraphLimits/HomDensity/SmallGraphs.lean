/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic

/-!
# Homomorphism densities of the smallest graphs

The two homomorphism densities that the rest of the theory quotes by name:

```text
t(K₂, W) = ∫∫ W(x, y)                              the edge density
t(K₃, W) = ∫∫∫ W(x, y) W(x, z) W(y, z)             the triangle density
```

Each is `homDensity` at a concrete graph, evaluated by transporting the integral over the function
space `Fin n → Ω` to an integral over a product `Ω × ⋯ × Ω`.  The transport is a measure-preserving
measurable equivalence supplied by Mathlib (`measurePreserving_piFinTwo` and
`measurePreserving_piFinSuccAbove`), so nothing here re-proves a Fubini theorem; the only work is
identifying the edge set of each graph and matching the factors.

**The vertex sets are `Fin 2` and `Fin 3`, and the graphs are `⊤`.**  Both edge sets are computed by
`decide`, which is what keeps these proofs short.  This is a catalogue of concrete values, not a
general schema: a statement covering all complete graphs at once would need an induction that the
`Fin n → Ω` transport does not currently support.

## Main results

* `homDensity_top_fin_two` — the edge density, as an integral against `μ.prod μ`;
* `homDensity_top_fin_three` — the triangle density, as an integral against `μ.prod (μ.prod μ)`.

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

/-- **The edge density.** The homomorphism density of the one-edge graph `K₂` is the integral of
the graphon over the whole square. -/
theorem homDensity_top_fin_two (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 2)) W = ∫ p : Ω × Ω, W p.1 p.2 ∂(μ.prod μ) := by
  have hedge : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by decide
  have hmp := measurePreserving_piFinTwo (fun _ : Fin 2 => μ)
  rw [homDensity_def, hedge, ← hmp.integral_comp (MeasurableEquiv.piFinTwo _).measurableEmbedding
    (fun p : Ω × Ω => W p.1 p.2)]
  have key : ∀ x : Fin 2 → Ω,
      ∏ e ∈ ({s(0, 1)} : Finset (Sym2 (Fin 2))), edgeFactor W x e = W (x 0) (x 1) := by
    intro x
    rw [Finset.prod_singleton, edgeFactor_mk]
  exact integral_congr_ae (ae_of_all _ fun x => key x)

/-- The transport from three independent coordinates to a triple product, as a measurable
equivalence.  It sends `x` to `(x 0, x 1, x 2)` definitionally. -/
private def piFinThreeEquiv (Ω : Type*) [MeasurableSpace Ω] : (Fin 3 → Ω) ≃ᵐ Ω × Ω × Ω :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Ω) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Ω) (MeasurableEquiv.piFinTwo _))

private theorem measurePreserving_piFinThreeEquiv (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (piFinThreeEquiv Ω) (Measure.pi fun _ : Fin 3 => μ) (μ.prod (μ.prod μ)) :=
  ((MeasurePreserving.id μ).prod (measurePreserving_piFinTwo (fun _ : Fin 2 => μ))).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0)

/-- **The triangle density.** The homomorphism density of `K₃` is the integral of the product of
the graphon over the three edges of a triple of points. -/
theorem homDensity_top_fin_three (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W
      = ∫ p : Ω × Ω × Ω, W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2 ∂(μ.prod (μ.prod μ)) := by
  have hedge : (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by decide
  have key : ∀ x : Fin 3 → Ω,
      ∏ e ∈ ({s(0, 1), s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 3))), edgeFactor W x e
        = W (x 0) (x 1) * W (x 0) (x 2) * W (x 1) (x 2) := by
    intro x
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    simp only [edgeFactor_mk]
    ring
  rw [homDensity_def, hedge,
    ← (measurePreserving_piFinThreeEquiv μ).integral_comp
      (piFinThreeEquiv Ω).measurableEmbedding
      (fun p : Ω × Ω × Ω => W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2)]
  exact integral_congr_ae (ae_of_all _ fun x => key x)

end DenseGraphLimits

end TauCeti
