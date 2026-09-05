/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Diffeomorph

/-!
# Images and local flatness under smooth ambient isotopy

The smooth ambient-isotopy relation on bundled embeddings is defined by a diffeotopy of the
ambient manifold.  This file exposes the geometric consequences of that definition which are
needed by knot and locally-flat embedding APIs: a witness transports the embedded image by its
final diffeomorphism, and local flatness is invariant under the relation.

The statements are deliberately about the existing `SmoothEmbedding.SmoothAmbientIsotopic`
relation.  They add no new knot representation; a smooth circle presentation inherits them by
specialisation of the source and target manifolds.

## Main results

* `SmoothAmbientIsotopic.range_eq_image_of_diffeotopy`: a diffeotopy witness identifies the two
  embedded images.
* `SmoothAmbientIsotopic.exists_range_eq_image`: every smooth ambient isotopy transports the image
  by the final diffeomorphism of a witness.
* `SmoothAmbientIsotopic.isLocallyFlat_iff`: local flatness is invariant under smooth ambient
  isotopy.

These results let downstream presentation theories reason about an embedded image without
unpacking the diffeotopy witness, and transfer the locally-flat hypotheses used by topological
embedding theorems.
-/

public section

noncomputable section

namespace TauCeti

open Set
open scoped Manifold ContDiff

namespace SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}
  {f g : SmoothEmbedding I J n M N}

namespace SmoothAmbientIsotopic

/-- A specified diffeotopy witness carries the image of one embedding to the other. -/
theorem range_eq_image_of_diffeotopy (Φ : Diffeotopy J n N)
    (hΦ : ∀ x, Φ.final (f x) = g x) :
    Φ.final '' range f = range g := by
  have hcomp : (Φ.final ∘ f : M → N) = g := by
    funext x
    exact hΦ x
  rw [← Set.range_comp, hcomp]

/-- A smooth ambient isotopy transports the embedded image by the final map of a witness. -/
theorem exists_range_eq_image (hfg : SmoothAmbientIsotopic f g) :
    ∃ Φ : Diffeotopy J n N, Φ.final '' range f = range g := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  exact ⟨Φ, range_eq_image_of_diffeotopy Φ hΦ⟩

/-- Local flatness is preserved when a smooth ambient isotopy carries one embedding to another. -/
theorem isLocallyFlat_of_smoothAmbientIsotopic {F F' : Type*} [TopologicalSpace F]
    [TopologicalSpace F'] [Zero F']
    (hfg : SmoothAmbientIsotopic f g) (hf : IsLocallyFlat F F' f) :
    IsLocallyFlat F F' g := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  have hcomp : (Φ.final.toHomeomorph : N ≃ₜ N) ∘ f = g := by
    funext x
    exact hΦ x
  rw [← hcomp]
  exact hf.homeomorph_comp Φ.final.toHomeomorph

/-- Local flatness is an invariant of smooth ambient-isotopy classes of embeddings. -/
theorem isLocallyFlat_iff {F F' : Type*} [TopologicalSpace F] [TopologicalSpace F'] [Zero F']
    (hfg : SmoothAmbientIsotopic f g) :
    IsLocallyFlat F F' f ↔ IsLocallyFlat F F' g := by
  constructor
  · exact isLocallyFlat_of_smoothAmbientIsotopic hfg
  · exact isLocallyFlat_of_smoothAmbientIsotopic hfg.symm

end SmoothAmbientIsotopic

end SmoothEmbedding

end TauCeti
