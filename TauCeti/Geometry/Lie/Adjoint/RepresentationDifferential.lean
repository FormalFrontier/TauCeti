/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
public import TauCeti.Geometry.Lie.Adjoint.Representation

/-!
# The differential of the adjoint representation

The differential at the identity of the group adjoint representation is Mathlib's Lie-algebra
adjoint map. This is the roadmap-facing form of the infinitesimal adjoint identity, stated on the
canonical Lie algebra of left-invariant derivations.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `TauCeti.Lie.mvfderiv_Ad_apply_one`: the identity `d(Ad)_1(X)(Y) = ad X Y`.
* `TauCeti.Lie.mvfderiv_continuousAdjointRepresentation_one`: the operator identity
  `d(Ad)_1(X) = ad X`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- Mathlib's algebraic adjoint map, regarded as a bounded operator on the finite-dimensional Lie
algebra. -/
def adContinuousLinearMap (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  exact LinearMap.toContinuousLinearMap
    (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X)

@[simp]
theorem adContinuousLinearMap_apply (X Y : LeftInvariantDerivation I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    adContinuousLinearMap (I := I) X Y =
      LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X Y := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  rw [adContinuousLinearMap]
  rfl

/-- The differential at the identity of the group adjoint action, evaluated on `X` and `Y`, is
the Lie-algebra adjoint `ad X Y`. -/
theorem mvfderiv_Ad_apply_one (X Y : LeftInvariantDerivation I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    mvfderiv I (fun g : G => Ad (I := I) g Y) 1
        (leftInvariantDerivationLieEquivGroupLieAlgebra
          (I := I) (G := G) BoundarylessManifold.isInteriorPoint X) =
      LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X Y := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let eLie := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  let eIso := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)
  let L : E → LeftInvariantDerivation I G := eIso.symm.toContinuousLinearEquiv
  let T : G → E := fun g => show E from tangentAd (I := I) g (eLie Y)
  have hT : ContMDiff I 𝓘(ℝ, E) ∞ T := by
    have hpair : ContMDiff I
        (I.prod 𝓘(ℝ, E)) ∞
        (fun g : G => (g, show E from eLie Y)) := contMDiff_id.prodMk contMDiff_const
    exact (contMDiff_tangentAd_apply (I := I) (G := G)).comp hpair
  have hEq : (fun g : G => Ad (I := I) g Y) = L ∘ T := by
    funext g
    simp only [Function.comp_apply, Ad_apply]
    change eLie.symm (tangentAd (I := I) g (eLie Y)) =
      L (show E from tangentAd (I := I) g (eLie Y))
    rw [leftInvariantDerivationLieEquivGroupLieAlgebra_symm_apply]
    change tangentToLeftInvariantDerivation (tangentAd (I := I) g (eLie Y)) =
      eIso.symm (show E from tangentAd (I := I) g (eLie Y))
    exact (leftInvariantDerivationLinearIsometryEquivModelVectorSpace_symm_apply
      (I := I) (G := G) (show E from tangentAd (I := I) g (eLie Y))).symm
  have hL : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, LeftInvariantDerivation I G) ∞ L :=
    eIso.symm.toContinuousLinearEquiv.contDiff.contMDiff
  rw [hEq, mvfderiv, ContinuousLinearMap.comp_apply]
  rw [mfderiv_comp_apply (1 : G)
    (hL.mdifferentiable (by simp) (T 1))
    (hT.mdifferentiable (by simp) 1) (eLie X)]
  have hLmf :=
    (eIso.symm.toContinuousLinearEquiv.hasFDerivAt (x := T 1)).hasMFDerivAt
  simp only [L]
  rw [hLmf.mfderiv]
  have hTangent := mvfderiv_tangentAd_apply_one (I := I) (G := G) (eLie X) (eLie Y)
  change
    (mfderiv I 𝓘(ℝ, E) T 1) (eLie X) =
      (show E from LieAlgebra.ad ℝ (GroupLieAlgebra I G) (eLie X) (eLie Y)) at hTangent
  rw [hTangent]
  simp only [LieAlgebra.ad_apply]
  rw [← eLie.map_lie]
  change eIso.symm (show E from eLie (⁅X, Y⁆)) = ⁅X, Y⁆
  calc
    eIso.symm (show E from eLie (⁅X, Y⁆)) = eLie.symm (eLie (⁅X, Y⁆)) := by
      rw [leftInvariantDerivationLieEquivGroupLieAlgebra_symm_apply]
      exact leftInvariantDerivationLinearIsometryEquivModelVectorSpace_symm_apply
        (I := I) (G := G) (show E from eLie (⁅X, Y⁆))
    _ = ⁅X, Y⁆ := eLie.symm_apply_apply _

/-- The differential at the identity of the bounded-operator-valued adjoint representation is
Mathlib's Lie-algebra adjoint map. -/
theorem mvfderiv_continuousAdjointRepresentation_one (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    mvfderiv I
      (continuousAdjointRepresentation (I := I) (G := G)) 1
      (leftInvariantDerivationLieEquivGroupLieAlgebra
        (I := I) (G := G) BoundarylessManifold.isInteriorPoint X) =
      adContinuousLinearMap (I := I) X := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let eLie := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  let dOp : LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G :=
    mvfderiv I
      (continuousAdjointRepresentation (I := I) (G := G)) 1 (eLie X)
  change
    dOp = adContinuousLinearMap (I := I) X
  apply ContinuousLinearMap.ext
  intro Y
  let evalY :
      (LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G) →L[ℝ]
        LeftInvariantDerivation I G :=
    (ContinuousLinearMap.apply ℝ (LeftInvariantDerivation I G)) Y
  have hOp :=
    (contMDiff_continuousAdjointRepresentation (I := I) (G := G)).mdifferentiable
      (by simp) (1 : G) |>.hasMFDerivAt
  have hEvalF : HasFDerivAt evalY evalY
      (continuousAdjointRepresentation (I := I) (G := G) 1) :=
    evalY.hasFDerivAt
  have hEval := hEvalF.hasMFDerivAt
  have hComp := hEval.comp (1 : G) hOp
  let AY : G → LeftInvariantDerivation I G := fun g => Ad (I := I) g Y
  have hCompAY : HasMFDerivAt I 𝓘(ℝ, LeftInvariantDerivation I G) AY 1
      (evalY.comp (mfderiv I
        𝓘(ℝ, LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G)
        (continuousAdjointRepresentation (I := I) (G := G)) 1)) := by
    apply hComp.congr_of_eventuallyEq
    filter_upwards [] with g
    simp only [AY, Function.comp_apply, evalY, ContinuousLinearMap.apply_apply,
      continuousAdjointRepresentation_apply]
  have hApply := congrArg (fun L => L (eLie X)) hCompAY.mfderiv.symm
  have hAYone : AY 1 = Y := by
    simpa only [AY, Ad_one] using
      (LieEquiv.refl_apply (R := ℝ) (L₁ := LeftInvariantDerivation I G) Y)
  rw [hAYone] at hApply
  have hApply' := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) Y) hApply
  have hLeft :
      NormedSpace.fromTangentSpace (𝕜 := ℝ) Y
        ((evalY.comp (mfderiv I
          𝓘(ℝ, LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G)
          (continuousAdjointRepresentation (I := I) (G := G)) 1)) (eLie X)) =
        dOp Y := by
    rfl
  have hRight :
      NormedSpace.fromTangentSpace (𝕜 := ℝ) Y
        ((mfderiv I 𝓘(ℝ, LeftInvariantDerivation I G) AY 1) (eLie X)) =
        mvfderiv I AY 1 (eLie X) := by
    rw [mvfderiv, ContinuousLinearMap.comp_apply, hAYone]
    rfl
  calc
    dOp Y = mvfderiv I AY 1 (eLie X) := by
      exact hLeft.symm.trans (hApply'.trans hRight)
    _ = LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X Y := by
      simpa only [AY, eLie] using mvfderiv_Ad_apply_one (I := I) (G := G) X Y
    _ = adContinuousLinearMap (I := I) X Y :=
      (adContinuousLinearMap_apply (I := I) X Y).symm

end TauCeti.Lie
