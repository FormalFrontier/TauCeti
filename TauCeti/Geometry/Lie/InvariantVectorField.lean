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
* `contMDiff_mulInvariantVectorField_modelSpace`: the invariant vector field is jointly `C^n` in
  its model-space generator and group argument when multiplication is `C^(n + 1)`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
* The proofs of `contMDiff_mulInvariantVectorField_modelSpace` and
  `contMDiff_mulInvariantVectorField_infty` adapt Sébastien Gouëzel's proof of Mathlib's
  `contMDiff_mulInvariantVectorField`.
-/

public section

open Bundle Function Manifold VectorField
open scoped ContDiff LieGroup Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- In model coordinates, the invariant vector field is jointly `C^n` in its generating tangent
vector and the group point when multiplication is `C^(n + 1)`. -/
theorem contMDiff_mulInvariantVectorField_modelSpace {n : ℕ∞ω}
    [ContMDiffMul I (n + 1) G] :
    let _ : IsManifold I 1 G := IsManifold.of_le (n := n + 1) le_add_self
    ContMDiff (𝓘(𝕜, E).prod I) I.tangent n
      (fun p : E × G =>
        (mulInvariantVectorField (I := I) (G := G) p.1 p.2 : TangentBundle I G)) := by
  let _ : IsManifold I 1 G := IsManifold.of_le (n := n + 1) le_add_self
  let fg : E × G → TangentBundle I G := fun p => TotalSpace.mk' E p.2 0
  have sfg : ContMDiff (𝓘(𝕜, E).prod I) I.tangent n fg :=
    (contMDiff_zeroSection 𝕜 (TangentSpace I : G → Type _)).comp contMDiff_snd
  let fv : E × G → TangentBundle I G := fun p => TotalSpace.mk' E 1 p.1
  have sfv : ContMDiff (𝓘(𝕜, E).prod I) I.tangent n fv := by
    intro p
    rw [Bundle.contMDiffAt_totalSpace]
    constructor
    · simpa only [fv] using
        (contMDiffAt_const : ContMDiffAt (𝓘(𝕜, E).prod I) I n
          (fun _ : E × G => (1 : G)) p)
    · have hone : (1 : G) ∈ (extChartAt I (1 : G)).source := mem_extChartAt_source _
      have hfun :
          (fun q : E × G =>
            (trivializationAt E (TangentSpace I) ((fv p).proj) (fv q)).2) = fun q => q.1 := by
        funext q
        rw [TangentBundle.trivializationAt_apply]
        -- Both fibers are over `1`, so their coordinate change is the identity on the model space.
        change tangentCoordChange I (1 : G) (1 : G) (1 : G) q.1 = q.1
        rw [tangentCoordChange_self hone]
      rw [hfun]
      exact contMDiffAt_fst
  let F₁ : E × G → TangentBundle I G × TangentBundle I G := fun p => (fg p, fv p)
  have S₁ : ContMDiff (𝓘(𝕜, E).prod I) (I.tangent.prod I.tangent) n F₁ :=
    sfg.prodMk sfv
  let F₂ : TangentBundle I G × TangentBundle I G → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I G I G).symm
  have S₂ : ContMDiff (I.tangent.prod I.tangent) (I.prod I).tangent n F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap% (fun p : G × G => p.1 * p.2)
  have S₃ : ContMDiff (I.prod I).tangent I.tangent n F₃ :=
    (contMDiff_mul I (n + 1)).contMDiff_tangentMap le_rfl
  let S := (S₃.comp S₂).comp S₁
  convert! S with p
  · simp [F₁, F₂, F₃, fg, fv]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁, fg, fv]
    rw [mfderiv_prod_eq_add_apply
      ((contMDiff_mul I (n + 1)).mdifferentiableAt (by simp))]
    simp +instances [mulInvariantVectorField, equivTangentBundleProd]
    rfl

/-- A left-invariant vector field on a smooth Lie group is smooth. -/
theorem contMDiff_mulInvariantVectorField_infty
    [ContMDiffMul I ∞ G] (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞
      (fun g : G ↦ (mulInvariantVectorField v g : TangentBundle I G)) := by
  let _ : ContMDiffMul I (∞ + 1) G := by
    simpa using (inferInstance : ContMDiffMul I ∞ G)
  have h := contMDiff_mulInvariantVectorField_modelSpace (I := I) (G := G) (n := ∞)
  exact h.comp (contMDiff_const.prodMk contMDiff_id)
