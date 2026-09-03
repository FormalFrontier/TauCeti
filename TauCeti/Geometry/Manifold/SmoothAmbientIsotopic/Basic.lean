/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Basic

/-!
# The smooth ambient-isotopy equivalence relation

This file defines smooth ambient isotopy for arbitrary bundled smooth maps between real
manifolds. Two maps are smoothly ambient isotopic when the final diffeomorphism of a diffeotopy
of the codomain carries the first map to the second.

The relation is defined generally before its specialization to bundled smooth embeddings in
`TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic`, following the
GeometricTopology roadmap's encoding convention. Forgetting smoothness recovers
`TauCeti.AmbientIsotopic`.

## Main definitions

* `TauCeti.SmoothAmbientIsotopic`: smooth ambient isotopy of arbitrary bundled smooth maps.
* `TauCeti.SmoothAmbientIsotopic.setoid`: the resulting equivalence relation.

## Main results

* `TauCeti.SmoothAmbientIsotopic.refl`, `symm`, and `trans`: smooth ambient isotopy is an
  equivalence relation.
* `TauCeti.SmoothAmbientIsotopic.final_comp`: a map is smoothly ambient isotopic to its
  postcomposition with the time-one map of a diffeotopy.
* `TauCeti.SmoothAmbientIsotopic.precomp`: smooth ambient isotopy is preserved by precomposing
  both maps with a fixed smooth map.
* `TauCeti.SmoothAmbientIsotopic.ambientIsotopic`: smooth ambient isotopy implies continuous
  ambient isotopy.

## References

* G. Burde and H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 1, for ambient
  isotopy of knots.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §8.1, for smooth
  isotopies and diffeotopies.
-/

public section

noncomputable section

namespace TauCeti

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

variable {f g h : C^n⟮J, M; J', N⟯}

/-- Two bundled smooth maps are **smoothly ambient isotopic** when the final diffeomorphism of a
`C^n` diffeotopy of the codomain carries the first map to the second. -/
def SmoothAmbientIsotopic (f g : C^n⟮J, M; J', N⟯) : Prop :=
  ∃ Φ : Diffeotopy J' n N, Φ.final.toContMDiffMap.comp f = g

/-- Smooth ambient isotopy is witnessed by a diffeotopy whose final diffeomorphism postcomposes
the first smooth map to the second. -/
theorem smoothAmbientIsotopic_def :
    SmoothAmbientIsotopic f g ↔
      ∃ Φ : Diffeotopy J' n N, Φ.final.toContMDiffMap.comp f = g :=
  Iff.rfl

namespace SmoothAmbientIsotopic

/-- A diffeotopy carrying `f` to `g` witnesses their smooth ambient isotopy. -/
theorem of_diffeotopy (Φ : Diffeotopy J' n N)
    (hΦ : Φ.final.toContMDiffMap.comp f = g) : SmoothAmbientIsotopic f g :=
  ⟨Φ, hΦ⟩

/-- **Transport along a diffeotopy is an ambient isotopy.** A smooth map and its postcomposition
with the time-one map of a diffeotopy of the codomain are smoothly ambient isotopic: the diffeotopy
itself is the witness. -/
theorem final_comp (f : C^n⟮J, M; J', N⟯) (Φ : Diffeotopy J' n N) :
    SmoothAmbientIsotopic f (Φ.final.toContMDiffMap.comp f) :=
  ⟨Φ, rfl⟩

/-- Smooth ambient isotopy of smooth maps is reflexive. -/
@[refl]
theorem refl (f : C^n⟮J, M; J', N⟯) : SmoothAmbientIsotopic f f := by
  refine ⟨Diffeotopy.refl J' n N, ?_⟩
  ext x
  simp

/-- Smooth ambient isotopy of smooth maps is symmetric. -/
@[symm]
theorem symm (hfg : SmoothAmbientIsotopic f g) : SmoothAmbientIsotopic g f := by
  obtain ⟨Φ, hΦ⟩ := hfg
  refine ⟨Φ.symm, ContMDiffMap.ext fun x ↦ ?_⟩
  rw [ContMDiffMap.comp_apply]
  have hx : Φ.final (f x) = g x := DFunLike.congr_fun hΦ x
  rw [← hx, Φ.final_symm]
  exact Φ.final.symm_apply_apply (f x)

/-- Smooth ambient isotopy of smooth maps is transitive. -/
@[trans]
theorem trans (hfg : SmoothAmbientIsotopic f g) (hgh : SmoothAmbientIsotopic g h) :
    SmoothAmbientIsotopic f h := by
  obtain ⟨Φ, hΦ⟩ := hfg
  obtain ⟨Ψ, hΨ⟩ := hgh
  have hxΦ (x : M) : Φ.final (f x) = g x := by
    simpa only [ContMDiffMap.comp_apply, _root_.Diffeomorph.coe_coe] using
      DFunLike.congr_fun hΦ x
  have hxΨ (x : M) : Ψ.final (g x) = h x := by
    simpa only [ContMDiffMap.comp_apply, _root_.Diffeomorph.coe_coe] using
      DFunLike.congr_fun hΨ x
  refine ⟨Φ.trans Ψ, ContMDiffMap.ext fun x ↦ ?_⟩
  rw [ContMDiffMap.comp_apply, Diffeotopy.final_trans]
  calc
    Φ.final.trans Ψ.final (f x) = Ψ.final (Φ.final (f x)) := by
      simpa only [Function.comp_apply] using
        congr_fun (_root_.Diffeomorph.coe_trans Φ.final Ψ.final) (f x)
    _ = h x := by rw [hxΦ, hxΨ]

/-- Precomposing two smoothly ambient-isotopic maps with the same smooth map preserves the
relation: the witnessing diffeotopy of the codomain is unchanged. -/
theorem precomp {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {J'' : ModelWithCorners ℝ E'' H''}
    {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
    (hfg : SmoothAmbientIsotopic f g) (k : C^n⟮J'', M''; J, M⟯) :
    SmoothAmbientIsotopic (f.comp k) (g.comp k) := by
  obtain ⟨Φ, hΦ⟩ := hfg
  exact ⟨Φ, ContMDiffMap.ext fun x ↦ DFunLike.congr_fun hΦ (k x)⟩

/-- Smooth ambient isotopy implies continuous ambient isotopy after forgetting smoothness. -/
theorem ambientIsotopic (hfg : SmoothAmbientIsotopic f g) :
    AmbientIsotopic (toContinuousMap f) (toContinuousMap g) := by
  obtain ⟨Φ, hΦ⟩ := hfg
  apply ambientIsotopic_def.mpr
  refine ⟨Φ.toAmbientIsotopy, ?_⟩
  ext x
  rw [ContinuousMap.comp_apply, Diffeotopy.toAmbientIsotopy_final_apply]
  exact DFunLike.congr_fun hΦ x

/-- Smooth ambient isotopy is an equivalence relation on bundled smooth maps. -/
theorem equivalence :
    Equivalence (SmoothAmbientIsotopic (J := J) (J' := J') (n := n) (M := M) (N := N)) :=
  ⟨refl, fun hfg ↦ hfg.symm, fun hfg hgh ↦ hfg.trans hgh⟩

/-- The smooth-ambient-isotopy equivalence relation on bundled smooth maps. -/
def setoid (J : ModelWithCorners ℝ E H) (J' : ModelWithCorners ℝ E' H') (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] :
    Setoid C^n⟮J, M; J', N⟯ where
  r := SmoothAmbientIsotopic
  iseqv := equivalence

/-- The relation of the smooth-ambient-isotopy setoid is smooth ambient isotopy. -/
@[simp]
theorem setoid_r_iff :
    (setoid J J' n M N).r f g ↔ SmoothAmbientIsotopic f g :=
  Iff.rfl

end SmoothAmbientIsotopic

end TauCeti
