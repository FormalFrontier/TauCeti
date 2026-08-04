/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Invariant vector fields on Lie groups

This file records regularity properties of invariant vector fields expressed through Mathlib's
tangent Lie algebra. These results depend only on `GroupLieAlgebra`, not on the separate
left-invariant-derivation model of a Lie algebra.

## Main results

* `contMDiff_mulInvariantVectorField_infty`: a left-invariant vector field on a smooth Lie group is
  smooth.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
* The proof of `contMDiff_mulInvariantVectorField_infty` follows Sébastien Gouëzel's proof of
  Mathlib's `contMDiff_mulInvariantVectorField`, specialized to infinite smoothness.
-/

public section

open Bundle Function Manifold VectorField
open scoped ContDiff LieGroup Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- A left-invariant vector field on a smooth Lie group is smooth. -/
theorem contMDiff_mulInvariantVectorField_infty
    [ContMDiffMul I ∞ G] (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞
      (fun g : G ↦ (mulInvariantVectorField v g : TangentBundle I G)) := by
  let fg : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sfg : ContMDiff I I.tangent ∞ fg := contMDiff_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ ↦ TotalSpace.mk' E 1 v
  have sfv : ContMDiff I I.tangent ∞ fv := contMDiff_const
  let F₁ : G → TangentBundle I G × TangentBundle I G := fun g ↦ (fg g, fv g)
  have S₁ : ContMDiff I (I.tangent.prod I.tangent) ∞ F₁ := sfg.prodMk sfv
  let F₂ : TangentBundle I G × TangentBundle I G →
      TangentBundle (I.prod I) (G × G) := (equivTangentBundleProd I G I G).symm
  have S₂ : ContMDiff (I.tangent.prod I.tangent) (I.prod I).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap% (fun p : G × G ↦ p.1 * p.2)
  have S₃ : ContMDiff (I.prod I).tangent I.tangent ∞ F₃ :=
    (contMDiff_mul I ∞).contMDiff_tangentMap (by simp)
  let S := (S₃.comp S₂).comp S₁
  convert! S with g
  · simp [F₁, F₂, F₃, fg, fv]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁, fg, fv]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I ∞).mdifferentiableAt (by simp))]
    simp +instances [mulInvariantVectorField, equivTangentBundleProd]
    rfl
