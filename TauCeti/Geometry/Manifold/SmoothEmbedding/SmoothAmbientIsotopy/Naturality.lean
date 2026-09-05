/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Manifold.SmoothAmbientIsotopic.Basic
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Complement

/-!
# Images and local flatness under smooth ambient isotopy

The smooth ambient-isotopy relation on bundled smooth maps is defined by a diffeotopy of the
ambient manifold.  This file exposes the geometric consequences of that definition which are
needed by knot and locally-flat embedding APIs: a witness transports an image by its final
diffeomorphism, and local flatness is invariant under the relation.  The statements are made at
the general smooth-map level, so the embedding specialization is available by coercion.

## Main results

* `SmoothAmbientIsotopic.image_range_eq_range_of_diffeotopy`: a diffeotopy witness identifies the
  two images.
* `SmoothAmbientIsotopic.exists_image_range_eq_range`: every smooth ambient isotopy transports the
  image by the final diffeomorphism of a witness.
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}
  {f g : C^n⟮I, M; J, N⟯}

namespace SmoothAmbientIsotopic

/-- A specified diffeotopy witness carries the image of one smooth map to the other. -/
theorem image_range_eq_range_of_diffeotopy (Φ : Diffeotopy J n N)
    (hΦ : Φ.final.toContMDiffMap.comp f = g) :
    Φ.final '' range f = range g := by
  have hΦ' : (Φ.toAmbientIsotopy.final.comp (toContinuousMap f) : M → N) = g := by
    ext x
    rw [ContinuousMap.comp_apply, Diffeotopy.toAmbientIsotopy_final_apply]
    change Φ.final (f x) = g x
    simpa only [ContMDiffMap.comp_apply, _root_.Diffeomorph.coe_coe] using DFunLike.congr_fun hΦ x
  have hfinal : (Φ.final : N → N) = Φ.toAmbientIsotopy.finalHomeomorph := by
    funext x
    calc
      Φ.final x = Φ.toAmbientIsotopy.final x :=
        (Φ.toAmbientIsotopy_final_apply x).symm
      _ = Φ.toAmbientIsotopy.finalHomeomorph x :=
        (Φ.toAmbientIsotopy.finalHomeomorph_apply x).symm
  rw [hfinal]
  have hrange : range (f : M → N) = range (toContinuousMap f) := rfl
  rw [hrange, ← hΦ']
  exact (Φ.toAmbientIsotopy.range_final_comp (toContinuousMap f)).symm

/-- A smooth ambient isotopy transports the embedded image by the final map of a witness. -/
theorem exists_image_range_eq_range (hfg : SmoothAmbientIsotopic f g) :
    ∃ Φ : Diffeotopy J n N, Φ.final '' range f = range g := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  exact ⟨Φ, image_range_eq_range_of_diffeotopy Φ hΦ⟩

/-- Local flatness is preserved when a smooth ambient isotopy carries one embedding to another. -/
theorem isLocallyFlat {F F' : Type*} [TopologicalSpace F]
    [TopologicalSpace F'] [Zero F']
    (hfg : SmoothAmbientIsotopic f g) (hf : IsLocallyFlat F F' f) :
    IsLocallyFlat F F' g := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  have hcomp : (Φ.final.toHomeomorph : N ≃ₜ N) ∘ f = g := by
    funext x
    simpa only [Function.comp_apply, ContMDiffMap.comp_apply,
      _root_.Diffeomorph.coe_toHomeomorph, _root_.Diffeomorph.coe_coe] using
      DFunLike.congr_fun hΦ x
  rw [← hcomp]
  exact hf.homeomorph_comp Φ.final.toHomeomorph

/-- Local flatness is an invariant of smooth ambient-isotopy classes of embeddings. -/
theorem isLocallyFlat_iff {F F' : Type*} [TopologicalSpace F] [TopologicalSpace F'] [Zero F']
    (hfg : SmoothAmbientIsotopic f g) :
    IsLocallyFlat F F' f ↔ IsLocallyFlat F F' g := by
  constructor
  · exact isLocallyFlat hfg
  · exact isLocallyFlat hfg.symm

end SmoothAmbientIsotopic

end TauCeti
