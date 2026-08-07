/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smoothness of the tangent adjoint action

The differential of conjugation depends smoothly on both the conjugating group element and the
tangent vector. Mathlib's smoothness theorem for manifold derivatives expresses the derivative in a
moving chart frame. Since conjugation fixes the identity, this file cancels the resulting fixed
tangent trivialization to recover the unframed tangent adjoint action.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `TauCeti.Lie.contMDiff_tangentAd_apply`: the joint action `(g, X) ↦ tangentAd g X` is smooth.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

noncomputable section

namespace TauCeti.Lie

open Manifold
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

omit [FiniteDimensional ℝ E] in
private theorem cancel_inCoordinates_at (x : G)
    (ϕ : TangentSpace I x →L[ℝ] TangentSpace I x) (v : TangentSpace I x) :
    let e := trivializationAt E (TangentSpace I) x
    e.symmL ℝ x
      (ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        x x x x ϕ (e.continuousLinearMapAt ℝ x v)) = ϕ v := by
  dsimp only
  rw [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    Bundle.Trivialization.symmL_continuousLinearMapAt,
    Bundle.Trivialization.symmL_continuousLinearMapAt] <;>
    exact FiberBundle.mem_baseSet_trivializationAt' x

omit [FiniteDimensional ℝ E] in
private theorem contMDiff_mfderiv_conj_apply :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : G × E ↦ @id E
        (mfderiv I I (conjDiffeomorph (I := I) (n := 3) p.1) 1
          (show TangentSpace I (1 : G) from p.2))) := by
  intro p
  let e := trivializationAt E (TangentSpace I) (1 : G)
  let A : TangentSpace I (1 : G) →L[ℝ] E := e.continuousLinearMapAt ℝ 1
  let B : E →L[ℝ] TangentSpace I (1 : G) := e.symmL ℝ 1
  let Amodel : E →L[ℝ] E := A
  let Bmodel : E →L[ℝ] E := B
  have he : (1 : G) ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' 1
  let f : G → G → G := fun g x ↦ g * x * g⁻¹
  let c : G → G := fun _ ↦ 1
  have hf : CMDiffAt ∞ (Function.uncurry f) (p.1, c p.1) := by
    exact (contMDiff_fst.mul contMDiff_snd).mul contMDiff_fst.inv |>.contMDiffAt
  have hA : CMDiffAt ∞ (fun x : G × E ↦ Amodel x.2) p :=
    Amodel.contMDiffAt.comp p contMDiffAt_snd
  have h := hf.mfderiv_apply (m := ∞) f c Prod.fst (fun x : G × E ↦ Amodel x.2)
    contMDiffAt_const contMDiffAt_fst hA (by simp)
  have hfc : (fun x ↦ f x (c x)) = c := by
    funext x
    simp [f, c]
  rw [hfc] at h
  have h' := Bmodel.contMDiffAt.comp p h
  convert h' using 1
  funext x
  let v : TangentSpace I (1 : G) := x.2
  change @id E ((mfderiv I I (conjDiffeomorph (I := I) (n := 3) x.1) 1) v) =
    @id E (B ((ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
      (1 : G) (1 : G) (1 : G) (1 : G) (mfderiv I I (f x.1) 1)) (A v)))
  have hcancel :
      B ((ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        (1 : G) (1 : G) (1 : G) (1 : G) (mfderiv I I (f x.1) 1)) (A v)) =
          (mfderiv I I (f x.1) 1) v := by
    dsimp only [A, B, e]
    exact cancel_inCoordinates_at (I := I) (G := G) (x := 1)
      (ϕ := mfderiv I I (f x.1) 1) (v := v)
  rw [hcancel]
  have hfun : (conjDiffeomorph (I := I) (n := 3) x.1 : G → G) = f x.1 := by
    funext y
    exact conjDiffeomorph_apply (I := I) (n := 3) x.1 y
  rw [mfderiv_congr hfun]
  rfl

/-- The tangent adjoint action is jointly smooth in the group element and tangent vector.

The explicit `id` fixes the codomain as the model space `E`; `GroupLieAlgebra I G` is definitionally
that space, but manifold typeclass search deliberately does not rely on this reduction. -/
theorem contMDiff_tangentAd_apply :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : G × E ↦ @id E
        (tangentAd (I := I) p.1 (show GroupLieAlgebra I G from p.2))) := by
  apply contMDiff_mfderiv_conj_apply (I := I) (G := G) |>.congr
  intro p
  let v : GroupLieAlgebra I G := p.2
  change @id E (tangentAd (I := I) p.1 v) =
    @id E ((mfderiv I I (conjDiffeomorph (I := I) (n := 3) p.1) 1) v)
  rw [tangentAd_apply, adjointContinuousLinearMap_apply]
  have hconj :
      (conjDiffeomorph (I := I) (n := 1) p.1 : G → G) =
        (conjDiffeomorph (I := I) (n := 3) p.1 : G → G) := by
    funext x
    simp only [conjDiffeomorph_apply]
  exact congrArg (fun L : E →L[ℝ] E ↦ @id E (L v)) (mfderiv_congr hconj)

end TauCeti.Lie
