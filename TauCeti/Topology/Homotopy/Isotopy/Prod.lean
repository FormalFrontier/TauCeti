/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.AmbientIsotopic.Basic

/-!
# Products of isotopies and ambient isotopies

An isotopy is a homotopy through topological embeddings, and an ambient isotopy is a homotopy
from the identity whose total map is a homeomorphism. This file
records that both notions are closed under taking products: an isotopy `f₀ ≈ f₁` and an isotopy
`g₀ ≈ g₁` combine, *along the shared time parameter*, into an isotopy `f₀ × g₀ ≈ f₁ × g₁` of the
product maps, and likewise for ambient isotopies of a product space.

This supplies product infrastructure for the geometric-topology roadmap's general isotopy
substrate (`TauCetiRoadmap/GeometricTopology/README.md`, encoding conventions), where isotopy and
ambient isotopy are defined once before being specialised to locally flat isotopy, diffeotopies,
and knot equivalence. It is also the isotopy analogue of the product closure lemmas that the
roadmap's later local-flatness product API is expected to mirror. For `TauCeti.Isotopy`, the
construction follows Mathlib's product lemmas for embeddings (`Topology.IsEmbedding.prodMap`) and
homotopy (`ContinuousMap.Homotopy.prodMap`). For ambient isotopies, the two factors share one time
coordinate, so the homeomorphism statement uses the time-duplicating embedding
`(t, x, x') ↦ ((t, x), (t, x'))`.

## Main definitions

* `TauCeti.Isotopy.prodMap`: the product of an isotopy `f₀ ≈ f₁` and an isotopy `g₀ ≈ g₁`, an
  isotopy `f₀.prodMap g₀ ≈ f₁.prodMap g₁`.
* `TauCeti.AmbientIsotopy.prodCongr`: the product of an ambient isotopy of `Y` and one of `Y'`, an
  ambient isotopy of `Y × Y'`.

## Main results

* `TauCeti.Isotopic.prodMap`: the same closure on the isotopy *relation*.
* `TauCeti.AmbientIsotopy.final_prodCongr`: the final map of a product ambient isotopy
  is the product of the two final maps.
* `TauCeti.AmbientIsotopic.prodMap`: the product closure on the ambient-isotopy relation.
-/

public section

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {X X' Y Y' : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [TopologicalSpace Y] [TopologicalSpace Y']

/-- The time-duplicating map `(t, (x, x')) ↦ ((t, x), (t, x'))` is a topological embedding: it has
the continuous left inverse `((a, x), (b, x')) ↦ (a, (x, x'))`. -/
private theorem isEmbedding_dupTime :
    IsEmbedding fun p : I × (X × X') => ((p.1, p.2.1), (p.1, p.2.2)) := by
  refine IsEmbedding.of_comp (by fun_prop)
    (g := fun w : (I × X) × (I × X') => (w.1.1, (w.1.2, w.2.2))) (by fun_prop) ?_
  have : ((fun w : (I × X) × (I × X') => (w.1.1, (w.1.2, w.2.2))) ∘
      fun p : I × (X × X') => ((p.1, p.2.1), (p.1, p.2.2))) = id := by funext p; rfl
  rw [this]
  exact IsEmbedding.id

/-- The core embedding lemma used by the ambient-isotopy product. If `u` and `v` are embeddings of
`I × X → I × Y` and `I × X' → I × Y'` that preserve the time coordinate, then the
*merged* total map `(t, (x, x')) ↦ (t, ((u (t, x)).2, (v (t, x')).2))` reading both at the same
time `t` is an embedding. It factors as the time-duplicating embedding, then `u × v`, then the
projection identifying the two (equal) time coordinates. -/
theorem isEmbedding_mergeTotal {u : C(I × X, I × Y)} {v : C(I × X', I × Y')}
    (hu : IsEmbedding u) (hv : IsEmbedding v) (hu1 : ∀ p, (u p).1 = p.1)
    (hv1 : ∀ p, (v p).1 = p.1) :
    IsEmbedding fun p : I × (X × X') => (p.1, ((u (p.1, p.2.1)).2, (v (p.1, p.2.2)).2)) := by
  -- `u × v` precomposed with the time-duplicating embedding is an embedding.
  have hQ : IsEmbedding fun p : I × (X × X') => (u (p.1, p.2.1), v (p.1, p.2.2)) :=
    (hu.prodMap hv).comp isEmbedding_dupTime
  -- Recover that embedding from the merged total map: postcompose by `(t, (y, y')) ↦
  -- ((t, y), (t, y'))`, which on the image undoes the time identification thanks to `hu1`/`hv1`.
  refine IsEmbedding.of_comp (by fun_prop)
    (g := fun q : I × (Y × Y') => ((q.1, q.2.1), (q.1, q.2.2))) (by fun_prop) ?_
  have heq : (fun q : I × (Y × Y') => ((q.1, q.2.1), (q.1, q.2.2))) ∘
      (fun p : I × (X × X') => (p.1, ((u (p.1, p.2.1)).2, (v (p.1, p.2.2)).2)))
      = fun p : I × (X × X') => (u (p.1, p.2.1), v (p.1, p.2.2)) := by
    funext p
    exact Prod.ext (Prod.ext (hu1 (p.1, p.2.1)).symm rfl) (Prod.ext (hv1 (p.1, p.2.2)).symm rfl)
  rw [heq]
  exact hQ

namespace Isotopy

variable {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X', Y')}

/-- The **product of two isotopies**, sharing the time parameter: from an isotopy `f₀ ≈ f₁` and an
isotopy `g₀ ≈ g₁` build an isotopy `f₀.prodMap g₀ ≈ f₁.prodMap g₁` whose value at `(t, (x, x'))` is
`(F (t, x), G (t, x'))`. The underlying homotopy is Mathlib's `ContinuousMap.Homotopy.prodMap`,
and each slice is a product of embeddings. -/
def prodMap (F : Isotopy f₀ f₁) (G : Isotopy g₀ g₁) :
    Isotopy (f₀.prodMap g₀) (f₁.prodMap g₁) where
  toHomotopy := F.toHomotopy.prodMap G.toHomotopy
  prop' := fun t => (F.isEmbedding_apply t).prodMap (G.isEmbedding_apply t)

@[simp]
theorem prodMap_apply (F : Isotopy f₀ f₁) (G : Isotopy g₀ g₁) (p : I × (X × X')) :
    F.prodMap G p = (F (p.1, p.2.1), G (p.1, p.2.2)) := (rfl)

end Isotopy

namespace Isotopic

variable {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X', Y')}

/-- Products preserve the isotopy relation: if `f₀ ≈ f₁` and `g₀ ≈ g₁`, then
`f₀.prodMap g₀ ≈ f₁.prodMap g₁`. -/
theorem prodMap (h : Isotopic f₀ f₁) (h' : Isotopic g₀ g₁) :
    Isotopic (f₀.prodMap g₀) (f₁.prodMap g₁) :=
  of_isotopy ((isotopic_def.mp h).some.prodMap (isotopic_def.mp h').some)

end Isotopic

namespace AmbientIsotopy

/-- The **product of two ambient isotopies**, sharing the time parameter: from an ambient isotopy
`Φ` of `Y` and one `Ψ` of `Y'` build an ambient isotopy of `Y × Y'` whose value at `(t, (y, y'))`
is `(Φ (t, y), Ψ (t, y'))`. Its total map is a homeomorphism, being an embedding (by
`isEmbedding_mergeTotal`) and surjective (each factor is surjective at every time, by
`AmbientIsotopy.isHomeomorph_apply`). -/
def prodCongr (Φ : AmbientIsotopy Y) (Ψ : AmbientIsotopy Y') : AmbientIsotopy (Y × Y') where
  toContinuousMap :=
    ⟨fun p => (Φ.toContinuousMap (p.1, p.2.1), Ψ.toContinuousMap (p.1, p.2.2)), by fun_prop⟩
  isHomeomorph_total' := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨?_, ?_⟩
    · simpa only [totalMap_apply] using
        isEmbedding_mergeTotal Φ.isHomeomorph_total.isEmbedding
          Ψ.isHomeomorph_total.isEmbedding (fun p => by simp) (fun p => by simp)
    rintro ⟨t, z, z'⟩
    obtain ⟨y, hy⟩ := (Φ.isHomeomorph_apply t).surjective z
    obtain ⟨y', hy'⟩ := (Ψ.isHomeomorph_apply t).surjective z'
    exact ⟨(t, y, y'), Prod.ext rfl (Prod.ext hy hy')⟩
  map_zero_left' y := Prod.ext (Φ.map_zero_left y.1) (Ψ.map_zero_left y.2)

@[simp]
theorem prodCongr_apply (Φ : AmbientIsotopy Y) (Ψ : AmbientIsotopy Y') (p : I × (Y × Y')) :
    (Φ.prodCongr Ψ).toContinuousMap p =
      (Φ.toContinuousMap (p.1, p.2.1), Ψ.toContinuousMap (p.1, p.2.2)) := (rfl)

/-- The final map of a product ambient isotopy is the product of the two final maps. -/
@[simp 1100]
theorem final_prodCongr (Φ : AmbientIsotopy Y) (Ψ : AmbientIsotopy Y') (y : Y × Y') :
    (Φ.prodCongr Ψ).final y = (Φ.final y.1, Ψ.final y.2) := by
  rw [final_apply, prodCongr_apply, final_apply, final_apply]

end AmbientIsotopy

namespace AmbientIsotopic

variable {f f' : C(X, Y)} {g g' : C(X', Y')}

/-- Products preserve the ambient-isotopy relation: if `f` and `f'` are ambient isotopic in `Y` and
`g` and `g'` are ambient isotopic in `Y'`, then `f.prodMap g` and `f'.prodMap g'` are ambient
isotopic in `Y × Y'`, via the product ambient isotopy. -/
theorem prodMap (h : AmbientIsotopic f f') (h' : AmbientIsotopic g g') :
    AmbientIsotopic (f.prodMap g) (f'.prodMap g') := by
  obtain ⟨Φ, hΦ⟩ := ambientIsotopic_def.mp h
  obtain ⟨Ψ, hΨ⟩ := ambientIsotopic_def.mp h'
  subst f'
  subst g'
  refine ambientIsotopic_def.mpr ⟨Φ.prodCongr Ψ, ContinuousMap.ext fun p => ?_⟩
  exact AmbientIsotopy.final_prodCongr Φ Ψ ((f.prodMap g) p)

end AmbientIsotopic

end TauCeti
