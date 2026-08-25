/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy
public import TauCeti.Geometry.Manifold.SmoothEmbedding.ContinuousAmbientIsotopy.Basic

/-!
# Smooth ambient isotopy of smooth embeddings

Two bundled smooth embeddings are smoothly ambient isotopic when a diffeotopy of the codomain
carries the first embedding to the second at time one.  This is the smooth equivalence relation
needed by geometric knot presentations: unlike
`SmoothEmbedding.ContinuousAmbientIsotopic`, its witness is smooth in both time and the ambient
variable and every time slice is a diffeomorphism.

The definition is kept at the level of arbitrary real manifolds and arbitrary `C^n` embeddings;
smooth knots are obtained by taking the domain to be the circle and the codomain to be the
ambient 3-manifold.  Forgetting the diffeotopy's smoothness recovers continuous ambient isotopy.

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
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 2, for smooth isotopies.
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
  ∃ Φ : Diffeotopy J n N, ∀ x, Φ.final (f x) = g x

/-- Smooth ambient isotopy is witnessed by a diffeotopy whose final diffeomorphism carries the
first embedding pointwise to the second. -/
theorem smoothAmbientIsotopic_def :
    SmoothAmbientIsotopic f g ↔ ∃ Φ : Diffeotopy J n N, ∀ x, Φ.final (f x) = g x :=
  Iff.rfl

namespace SmoothAmbientIsotopic

/-- A diffeotopy carrying `f` to `g` witnesses their smooth ambient isotopy. -/
theorem of_diffeotopy (Φ : Diffeotopy J n N) (hΦ : ∀ x, Φ.final (f x) = g x) :
    SmoothAmbientIsotopic f g :=
  ⟨Φ, hΦ⟩

/-- Smooth ambient isotopy of embeddings is reflexive. -/
@[refl]
theorem refl (f : SmoothEmbedding I J n M N) : SmoothAmbientIsotopic f f :=
  ⟨Diffeotopy.refl J n N, fun x ↦ by simp⟩

/-- Smooth ambient isotopy of embeddings is symmetric. -/
@[symm]
theorem symm (hfg : SmoothAmbientIsotopic f g) : SmoothAmbientIsotopic g f := by
  obtain ⟨Φ, hΦ⟩ := hfg
  refine ⟨Φ.symm, fun x ↦ ?_⟩
  rw [← hΦ x]
  exact Φ.symm_final_final (f x)

/-- Smooth ambient isotopy of embeddings is transitive. -/
@[trans]
theorem trans (hfg : SmoothAmbientIsotopic f g) (hgh : SmoothAmbientIsotopic g h) :
    SmoothAmbientIsotopic f h := by
  obtain ⟨Φ, hΦ⟩ := hfg
  obtain ⟨Ψ, hΨ⟩ := hgh
  refine ⟨Φ.trans Ψ, fun x ↦ ?_⟩
  rw [Diffeotopy.final_trans, hΦ x, hΨ x]

/-- Smooth ambient isotopy is an equivalence relation on bundled smooth embeddings. -/
theorem equivalence :
    Equivalence (SmoothAmbientIsotopic (I := I) (J := J) (n := n) (M := M) (N := N)) :=
  ⟨refl, fun hfg ↦ hfg.symm, fun hfg hgh ↦ hfg.trans hgh⟩

/-- Smooth ambient isotopy implies continuous ambient isotopy after forgetting the smoothness of
the witnessing diffeotopy. -/
theorem continuousAmbientIsotopic (hfg : SmoothAmbientIsotopic f g) :
    ContinuousAmbientIsotopic f g := by
  obtain ⟨Φ, hΦ⟩ := hfg
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
