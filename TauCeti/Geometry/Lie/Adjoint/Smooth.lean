/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smoothness of the tangent adjoint action

The differential of conjugation depends smoothly on the conjugating group element. Mathlib's
smoothness theorem for manifold derivatives expresses the derivative in a moving chart frame. Since
conjugation fixes the identity, this file cancels the resulting fixed tangent trivialization to
recover the unframed tangent adjoint operator and its jointly smooth evaluation action.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `TauCeti.Lie.contMDiff_adjointContinuousLinearMap`: the adjoint operator depends smoothly on the
  group element.
* `TauCeti.Lie.contMDiff_tangentAd_apply`: the bundled tangent adjoint action is jointly smooth.
* `TauCeti.Lie.contMDiff_tangentAd_apply_const`: the bundled tangent adjoint action on a fixed model
  vector is smooth in the group element.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
* Sébastien Gouëzel and Floris van Doorn's
  `Mathlib.Geometry.Manifold.ContMDiffMFDeriv`, especially `ContMDiffAt.mfderiv`, supplies
  smoothness of the conjugation differential in a fixed frame. The frame cancellation follows the
  argument for `Pretrivialization.continuousLinearMap` in `Mathlib.Topology.VectorBundle.Hom`.
-/

public section

noncomputable section

namespace TauCeti.Lie

open Manifold
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [CompleteSpace E] [LieGroup I ∞ G]

omit [CompleteSpace E] in
private theorem cancel_inCoordinates_at {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (x : M)
    (ϕ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    let e := trivializationAt E (TangentSpace I) x
    (e.symmL ℝ x).comp
      ((ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        x x x x ϕ).comp (e.continuousLinearMapAt ℝ x)) = ϕ := by
  apply ContinuousLinearMap.ext
  intro v
  have hcancel (w : TangentSpace I x) :
      (trivializationAt E (TangentSpace I) x).symmL ℝ x
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w) = w := by
    rw [Bundle.Trivialization.symmL_continuousLinearMapAt]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [hcancel, hcancel]

omit [CompleteSpace E] in
/-- The continuous linear operator underlying the tangent adjoint action depends smoothly on the
group element. -/
theorem contMDiff_adjointContinuousLinearMap :
    ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞
      -- `GroupLieAlgebra I G` definitionally reduces to the tangent model `E`; the ascription
      -- exposes that model to the normed-space smoothness API.
      (fun g : G ↦ show E →L[ℝ] E from adjointContinuousLinearMap (I := I) g) := by
  intro g
  let e := trivializationAt E (TangentSpace I) (1 : G)
  let A : TangentSpace I (1 : G) →L[ℝ] E := e.continuousLinearMapAt ℝ 1
  let B : E →L[ℝ] TangentSpace I (1 : G) := e.symmL ℝ 1
  let Amodel : E →L[ℝ] E := A
  let Bmodel : E →L[ℝ] E := B
  let f : G → G → G := fun g ↦ conjDiffeomorph (I := I) (n := 1) g
  let c : G → G := fun _ ↦ 1
  have hf : CMDiffAt ∞ (Function.uncurry f) (g, c g) := by
    rw [show Function.uncurry f = fun p : G × G ↦ p.1 * p.2 * p.1⁻¹ by
      funext p
      exact conjDiffeomorph_apply p.1 p.2]
    exact contMDiff_conj_prod (I := I) (n := ∞) _
  have h := hf.mfderiv (m := ∞) f c contMDiffAt_const (by simp)
  have hfc : (fun x ↦ f x (c x)) = c := by
    funext x
    simp [f, c]
  rw [hfc] at h
  have hA : CMDiffAt ∞ (fun _ : G ↦ Amodel) g := contMDiffAt_const
  have hB : CMDiffAt ∞ (fun _ : G ↦ Bmodel) g := contMDiffAt_const
  have h' := hB.clm_comp (h.clm_comp hA)
  convert h' using 1
  funext x
  -- Unfold the fixed source and target fibers hidden by `inTangentCoordinates`.
  change (adjointContinuousLinearMap (I := I) x : E →L[ℝ] E) =
    Bmodel.comp
      ((ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        (1 : G) (1 : G) (1 : G) (1 : G) (mfderiv I I (f x) 1)).comp Amodel)
  have hadj : (adjointContinuousLinearMap (I := I) x : E →L[ℝ] E) =
      mfderiv I I (conjDiffeomorph (I := I) (n := 1) x) 1 := by
    -- The public definitions from `Basic` are opaque here, so use its exported pointwise
    -- comparison theorem and extensionality to compare the operators.
    apply ContinuousLinearMap.ext
    intro v
    exact adjointContinuousLinearMap_apply (I := I) x v
  rw [hadj]
  dsimp only [f]
  symm
  dsimp only [Amodel, Bmodel, A, B, e]
  exact cancel_inCoordinates_at (I := I) (M := G) (x := 1)
    (ϕ := mfderiv I I (f x) 1)

/-- The bundled tangent adjoint action is jointly smooth in the group element and model vector. -/
theorem contMDiff_tangentAd_apply :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : G × E ↦
        show E from tangentAd (I := I) p.1 (p.2 : GroupLieAlgebra I G)) := by
  -- `GroupLieAlgebra I G` definitionally reduces to the model space `E`; expose that model-space
  -- presentation so the continuous-linear-map smoothness API applies.
  rw [show (fun p : G × E ↦
      show E from tangentAd (I := I) p.1 (p.2 : GroupLieAlgebra I G)) =
    fun p ↦ (show E →L[ℝ] E from adjointContinuousLinearMap (I := I) p.1) p.2 by
    funext p
    exact tangentAd_apply (I := I) p.1 p.2]
  exact ((contMDiff_adjointContinuousLinearMap (I := I) (G := G)).comp contMDiff_fst).clm_apply
    contMDiff_snd

/-- The bundled tangent adjoint action on a fixed model vector is smooth in the group element. -/
theorem contMDiff_tangentAd_apply_const (Y : E) :
    ContMDiff I 𝓘(ℝ, E) ∞
      (fun g : G ↦ show E from tangentAd (I := I) g (Y : GroupLieAlgebra I G)) := by
  -- `GroupLieAlgebra I G` definitionally reduces to the model space `E`; expose that model-space
  -- presentation when specializing the jointly smooth action to `Y`.
  exact (contMDiff_tangentAd_apply (I := I) (G := G)).comp
    (contMDiff_id.prodMk contMDiff_const)

end TauCeti.Lie
