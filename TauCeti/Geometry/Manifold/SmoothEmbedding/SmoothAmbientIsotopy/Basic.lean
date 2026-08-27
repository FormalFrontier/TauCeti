/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothAmbientIsotopic.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.ContinuousAmbientIsotopy.Basic

/-!
# Smooth ambient isotopy of smooth embeddings

This file specializes `TauCeti.SmoothAmbientIsotopic`, the smooth ambient-isotopy relation on
arbitrary bundled smooth maps, to bundled smooth embeddings.  Two embeddings are related when a
diffeotopy of the codomain carries the first to the second at time one.  This is the smooth
equivalence relation needed by geometric knot presentations: unlike
`SmoothEmbedding.ContinuousAmbientIsotopic`, its witness is smooth in both time and the ambient
variable and every time slice is a diffeomorphism.

The general relation is defined once for arbitrary `C^n` maps; this file's relation is its thin
specialization along `SmoothEmbedding.toContMDiffMap`. Smooth knots are obtained by taking the
domain to be the circle and the codomain to be the ambient 3-manifold. Forgetting the
diffeotopy's smoothness recovers continuous ambient isotopy.

This is the specialization of `TauCeti.Diffeotopy` requested by Layer 4 of the
GeometricTopology roadmap, in the milestone “equivalence in each presentation.”

## Main definitions

* `TauCeti.SmoothEmbedding.SmoothAmbientIsotopic`: smooth ambient isotopy of bundled smooth
  embeddings.
* `TauCeti.SmoothEmbedding.SmoothAmbientIsotopic.setoid`: the resulting equivalence relation.

## Main results

* `SmoothAmbientIsotopic.refl`, `symm`, and `trans`: smooth ambient isotopy is an equivalence
  relation.
* `SmoothAmbientIsotopic.continuousAmbientIsotopic`: smoothly ambient isotopic embeddings are
  continuously ambient isotopic.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 1, for ambient
  isotopy as knot equivalence.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1, for smooth
  isotopies.
-/

public section

noncomputable section

namespace TauCeti

open scoped Manifold ContDiff

namespace SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

variable {f g h : SmoothEmbedding I J n M N}

/-- Two smooth embeddings are **smoothly ambient isotopic** when the final diffeomorphism of a
`C^n` diffeotopy of the codomain carries the first embedding to the second. -/
def SmoothAmbientIsotopic (f g : SmoothEmbedding I J n M N) : Prop :=
  TauCeti.SmoothAmbientIsotopic f.toContMDiffMap g.toContMDiffMap

/-- Smooth ambient isotopy is witnessed by a diffeotopy whose final diffeomorphism carries the
first embedding pointwise to the second. -/
theorem smoothAmbientIsotopic_def :
    SmoothAmbientIsotopic f g ↔ ∃ Φ : Diffeotopy J n N, ∀ x, Φ.final (f x) = g x := by
  constructor
  · intro hfg
    obtain ⟨Φ, hΦ⟩ := TauCeti.smoothAmbientIsotopic_def.mp hfg
    refine ⟨Φ, fun x ↦ ?_⟩
    simpa only [ContMDiffMap.comp_apply, _root_.Diffeomorph.coe_coe,
      SmoothEmbedding.toContMDiffMap_coe] using
      DFunLike.congr_fun hΦ x
  · rintro ⟨Φ, hΦ⟩
    apply TauCeti.smoothAmbientIsotopic_def.mpr
    refine ⟨Φ, ContMDiffMap.ext fun x ↦ ?_⟩
    simpa only [ContMDiffMap.comp_apply, _root_.Diffeomorph.coe_coe,
      SmoothEmbedding.toContMDiffMap_coe] using hΦ x

namespace SmoothAmbientIsotopic

/-- A diffeotopy carrying `f` to `g` witnesses their smooth ambient isotopy. -/
theorem of_diffeotopy (Φ : Diffeotopy J n N) (hΦ : ∀ x, Φ.final (f x) = g x) :
    SmoothAmbientIsotopic f g :=
  smoothAmbientIsotopic_def.mpr ⟨Φ, hΦ⟩

/-- Smooth ambient isotopy of embeddings is reflexive. -/
@[refl]
theorem refl (f : SmoothEmbedding I J n M N) : SmoothAmbientIsotopic f f :=
  TauCeti.SmoothAmbientIsotopic.refl f.toContMDiffMap

/-- Smooth ambient isotopy of embeddings is symmetric. -/
@[symm]
theorem symm (hfg : SmoothAmbientIsotopic f g) : SmoothAmbientIsotopic g f := by
  exact TauCeti.SmoothAmbientIsotopic.symm hfg

/-- Smooth ambient isotopy of embeddings is transitive. -/
@[trans]
theorem trans (hfg : SmoothAmbientIsotopic f g) (hgh : SmoothAmbientIsotopic g h) :
    SmoothAmbientIsotopic f h := by
  exact TauCeti.SmoothAmbientIsotopic.trans hfg hgh

/-- Smooth ambient isotopy is an equivalence relation on bundled smooth embeddings. -/
theorem equivalence :
    Equivalence (SmoothAmbientIsotopic (I := I) (J := J) (n := n) (M := M) (N := N)) :=
  ⟨refl, fun hfg ↦ hfg.symm, fun hfg hgh ↦ hfg.trans hgh⟩

/-- Smooth ambient isotopy implies continuous ambient isotopy after forgetting the smoothness of
the witnessing diffeotopy. -/
theorem continuousAmbientIsotopic (hfg : SmoothAmbientIsotopic f g) :
    ContinuousAmbientIsotopic f g := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  refine ContinuousAmbientIsotopic.of_ambientIsotopy Φ.toAmbientIsotopy ?_
  ext x
  rw [ContinuousMap.comp_apply, Diffeotopy.toAmbientIsotopy_final_apply]
  exact hΦ x

/-- Smooth ambient isotopy of bundled smooth embeddings, packaged as a setoid. -/
def setoid (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H') (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] :
    Setoid (SmoothEmbedding I J n M N) where
  r := SmoothAmbientIsotopic
  iseqv := equivalence

/-- The relation of the smooth-ambient-isotopy setoid is smooth ambient isotopy. -/
@[simp]
theorem setoid_r_iff : (setoid I J n M N).r f g ↔ SmoothAmbientIsotopic f g :=
  Iff.rfl

end SmoothAmbientIsotopic

end SmoothEmbedding

end TauCeti
