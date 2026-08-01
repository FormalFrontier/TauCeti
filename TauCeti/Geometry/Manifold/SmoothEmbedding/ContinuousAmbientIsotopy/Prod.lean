/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.ContinuousAmbientIsotopy.Basic
public import TauCeti.Topology.Homotopy.Isotopy.Prod

/-!
# Products of continuously ambient-isotopic smooth embeddings

The geometric-topology roadmap treats the geometric presentation of a knot or link as a smooth
embedding and asks that ambient isotopy be defined generally, then specialised to those
presentations. `TauCeti.Topology.Homotopy.Isotopy.Prod` proves product closure for the general
continuous ambient-isotopy relation, and `TauCeti.Geometry.Manifold.SmoothEmbedding.Basic` bundles
the product of smooth embeddings. This file connects those two APIs.

This is deliberately a thin specialisation: it does not introduce a knot type or a new isotopy
notion. It says that the product presentation built from two pairs of continuously ambient-isotopic
smooth embeddings is again continuously ambient isotopic, with the statement phrased entirely in
the bundled `SmoothEmbedding` API.

## Main results

* `TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic.prodMap`: products preserve continuous ambient
  isotopy of bundled smooth embeddings.
* `TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic.prodMap_setoid`: the same fact in
  setoid-relation form.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

namespace SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂]
  {G₁ : Type*} [TopologicalSpace G₁] {G₂ : Type*} [TopologicalSpace G₂]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {J₁ : ModelWithCorners 𝕜 F₁ G₁} {J₂ : ModelWithCorners 𝕜 F₂ G₂}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  {N₁ : Type*} [TopologicalSpace N₁] [ChartedSpace G₁ N₁]
  {N₂ : Type*} [TopologicalSpace N₂] [ChartedSpace G₂ N₂]
  {n : ℕ∞ω}

namespace ContinuousAmbientIsotopic

variable [IsManifold I₁ n M₁] [IsManifold I₂ n M₂] [IsManifold J₁ n N₁]
  [IsManifold J₂ n N₂]
  {f f' : SmoothEmbedding I₁ J₁ n M₁ N₁}
  {g g' : SmoothEmbedding I₂ J₂ n M₂ N₂}

/-- Products preserve continuous ambient isotopy of bundled smooth embeddings.

If `f` is continuously ambient isotopic to `f'` and `g` is continuously ambient isotopic to `g'`,
then the bundled product embedding `f.prodMap g` is continuously ambient isotopic to
`f'.prodMap g'`. This is the smooth-embedding specialisation of
`TauCeti.AmbientIsotopic.prodMap`. -/
theorem prodMap (hff' : ContinuousAmbientIsotopic f f') (hgg' : ContinuousAmbientIsotopic g g') :
    ContinuousAmbientIsotopic (f.prodMap g) (f'.prodMap g') := by
  rw [continuousAmbientIsotopic_def] at hff' hgg' ⊢
  exact TauCeti.ambientIsotopic_def.1 <| by
    simpa [toContinuousMap_prodMap] using
      TauCeti.AmbientIsotopic.prodMap (TauCeti.ambientIsotopic_def.2 hff')
        (TauCeti.ambientIsotopic_def.2 hgg')

/-- Product closure for the continuous-ambient-isotopy setoid on bundled smooth embeddings. -/
theorem prodMap_setoid (hff' : (setoid I₁ J₁ n M₁ N₁).r f f')
    (hgg' : (setoid I₂ J₂ n M₂ N₂).r g g') :
    (setoid (I₁.prod I₂) (J₁.prod J₂) n (M₁ × M₂) (N₁ × N₂)).r (f.prodMap g) (f'.prodMap g') :=
  setoid_r_iff.2 (prodMap (setoid_r_iff.1 hff') (setoid_r_iff.1 hgg'))

end ContinuousAmbientIsotopic

end SmoothEmbedding

end TauCeti
