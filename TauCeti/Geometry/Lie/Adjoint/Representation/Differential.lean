/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
import TauCeti.Geometry.Manifold.VectorField.Regularity
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic

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
  let T : G → E := fun g => show E from tangentAd (I := I) g (eIso Y)
  have hT : ContMDiff I 𝓘(ℝ, E) ∞ T :=
    contMDiff_tangentAd_apply_right (I := I) (G := G) (eIso Y)
  have hEq : (fun g : G => Ad (I := I) g Y) = L ∘ T := by
    funext g
    apply eIso.injective
    rw [leftInvariantDerivationLinearIsometryEquivModelVectorSpace_Ad]
    -- Unfold the local composition and use the explicit inverse law of the model equivalence.
    change tangentAd (I := I) g (eIso Y) = eIso (eIso.symm (T g))
    rw [eIso.apply_symm_apply]
  have hL : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, LeftInvariantDerivation I G) ∞ L :=
    eIso.symm.toContinuousLinearEquiv.contDiff.contMDiff
  rw [hEq]
  rw [mvfderiv_apply_eq_mfderiv_apply]
  rw [mfderiv_comp_apply (1 : G)
    (hL.mdifferentiable (by simp) (T 1))
    (hT.mdifferentiable (by simp) 1) (eLie X)]
  have hLmf :=
    (eIso.symm.toContinuousLinearEquiv.hasFDerivAt (x := T 1)).hasMFDerivAt
  simp only [L]
  rw [hLmf.mfderiv]
  have hTangent := mvfderiv_tangentAd_apply_one (I := I) (G := G) (eLie X)
    ((eIso Y : E) : GroupLieAlgebra I G)
  -- `GroupLieAlgebra I G` is definitionally the model vector space `E`; expose that canonical
  -- identification so the tangent-level derivative theorem can rewrite the model-valued map `T`.
  change
    (mfderiv I 𝓘(ℝ, E) T 1) (eLie X) =
      (show E from LieAlgebra.ad ℝ (GroupLieAlgebra I G) (eLie X)
        ((eIso Y : E) : GroupLieAlgebra I G)) at hTangent
  rw [hTangent]
  simp only [LieAlgebra.ad_apply]
  have heIsoLieY : ((eIso Y : E) : GroupLieAlgebra I G) = eLie Y := by
    exact leftInvariantDerivationLinearIsometryEquivModelVectorSpace_eq_lieEquiv
      (I := I) (G := G) BoundarylessManifold.isInteriorPoint Y
  rw [heIsoLieY]
  have hbracket := eLie.map_lie X Y
  -- Expose the bracket-valued model vector produced by `LieAlgebra.ad` so the Lie equivalence's
  -- explicit bracket-preservation theorem can rewrite it.
  change eIso.symm (show E from (⁅eLie X, eLie Y⁆ : GroupLieAlgebra I G)) = ⁅X, Y⁆
  rw [← hbracket]
  -- Expose the model-space coercion so the shared inverse-transport fact applies.
  change eIso.symm (show E from eLie (⁅X, Y⁆)) = ⁅X, Y⁆
  rw [leftInvariantDerivationLinearIsometryEquivModelVectorSpace_symm_eq_lieEquiv_symm
      (I := I) (G := G) BoundarylessManifold.isInteriorPoint,
    eLie.symm_apply_apply]

/-- The differential at the identity of the bounded-operator-valued adjoint representation is
Mathlib's Lie-algebra adjoint map. -/
theorem mvfderiv_continuousAdjointRepresentation_one (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
      finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
    mvfderiv I
      (continuousAdjointRepresentation (I := I) (G := G)) 1
      (leftInvariantDerivationLieEquivGroupLieAlgebra
        (I := I) (G := G) BoundarylessManifold.isInteriorPoint X) =
      LinearMap.toContinuousLinearMap
        (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  let eLie := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  let dOp : LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G :=
    mvfderiv I
      (continuousAdjointRepresentation (I := I) (G := G)) 1 (eLie X)
  -- Unfold only the local abbreviation; the target stays in Mathlib's canonical operator API.
  change dOp = LinearMap.toContinuousLinearMap
    (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X)
  apply ContinuousLinearMap.ext
  intro Y
  let evalY :
      (LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G) →L[ℝ]
        LeftInvariantDerivation I G :=
    (ContinuousLinearMap.apply ℝ (LeftInvariantDerivation I G)) Y
  let AY : G → LeftInvariantDerivation I G := fun g => Ad (I := I) g Y
  have hComp := mfderiv_comp_apply (I := I) (I' :=
      𝓘(ℝ, LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G))
    (I'' := 𝓘(ℝ, LeftInvariantDerivation I G))
    (1 : G)
    evalY.mdifferentiableAt
    ((contMDiff_continuousAdjointRepresentation (I := I) (G := G)).mdifferentiable
      (by simp) 1)
    (eLie X)
  rw [evalY.hasMFDerivAt.mfderiv] at hComp
  have hAY : AY = evalY ∘ continuousAdjointRepresentation (I := I) (G := G) := by
    funext g
    exact (continuousAdjointRepresentation_apply (I := I) g Y).symm
  have hCompAY :
      mvfderiv I AY 1 (eLie X) = dOp Y := by
    rw [hAY, mvfderiv_apply_eq_mfderiv_apply, hComp]
    change ((ContinuousLinearMap.apply ℝ (LeftInvariantDerivation I G)) Y) dOp = dOp Y
    rfl
  calc
    dOp Y = mvfderiv I AY 1 (eLie X) := hCompAY.symm
    _ = LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X Y := by
      simpa only [AY, eLie] using mvfderiv_Ad_apply_one (I := I) (G := G) X Y
    _ = LinearMap.toContinuousLinearMap
        (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X) Y := by
      rw [LinearMap.coe_toContinuousLinearMap']

end TauCeti.Lie
