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

* `TauCeti.Lie.mfderiv_Ad_apply_one`: the identity `d(Ad)_1(X)(Y) = ad X Y`.
* `TauCeti.Lie.mfderiv_continuousAdjointRepresentation_one`: the operator identity
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

private theorem modelBracketTransport (X Y : LeftInvariantDerivation I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let eLie := leftInvariantDerivationLieEquivGroupLieAlgebra
      (I := I) (G := G) BoundarylessManifold.isInteriorPoint
    let eIso := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
      (I := I) (G := G)
    eIso.symm (show E from (⁅eLie X, eLie Y⁆ : GroupLieAlgebra I G)) = ⁅X, Y⁆ := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let eLie := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  let eIso := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)
  calc
    eIso.symm (show E from (⁅eLie X, eLie Y⁆ : GroupLieAlgebra I G)) =
        tangentToLeftInvariantDerivation (I := I) (G := G) ⁅eLie X, eLie Y⁆ :=
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace_symm_apply
        (I := I) (G := G) (show E from (⁅eLie X, eLie Y⁆ : GroupLieAlgebra I G))
    _ = ⁅tangentToLeftInvariantDerivation (I := I) (G := G) (eLie X),
        tangentToLeftInvariantDerivation (I := I) (G := G) (eLie Y)⁆ :=
      tangentToLeftInvariantDerivation_lie (I := I) (G := G) (eLie X) (eLie Y)
    _ = ⁅eIso.symm (show E from eLie X), eIso.symm (show E from eLie Y)⁆ := by
      rw [leftInvariantDerivationLinearIsometryEquivModelVectorSpace_symm_apply,
        leftInvariantDerivationLinearIsometryEquivModelVectorSpace_symm_apply]
    _ = ⁅X, Y⁆ := by
      rw [leftInvariantDerivationLinearIsometryEquivModelVectorSpace_symm_lieEquiv_apply,
        leftInvariantDerivationLinearIsometryEquivModelVectorSpace_symm_lieEquiv_apply]

/-- The differential at the identity of the group adjoint action, evaluated on `X` and `Y`, is
the Lie-algebra adjoint `ad X Y`. -/
@[simp]
theorem mfderiv_Ad_apply_one (X Y : LeftInvariantDerivation I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    (show LeftInvariantDerivation I G from
      mfderiv I 𝓘(ℝ, LeftInvariantDerivation I G) (fun g : G => Ad (I := I) g Y) 1
        (pointDerivationEquivTangentSpace (I := I) 1
          BoundarylessManifold.isInteriorPoint (LeftInvariantDerivation.evalAt 1 X))) =
      LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X Y := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let eLie := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  let eIso := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)
  let L : E → LeftInvariantDerivation I G := eIso.symm.toContinuousLinearEquiv
  -- `GroupLieAlgebra I G` is definitionally the model space `E`, so the tangent orbit is
  -- model-space-valued here.
  let T : G → E := fun g => show E from tangentAd (I := I) g (eIso Y)
  have hT : ContMDiff I 𝓘(ℝ, E) ∞ T :=
    contMDiff_tangentAd_apply_right (I := I) (G := G) (eIso Y)
  have hEq : (fun g : G => Ad (I := I) g Y) = L ∘ T := by
    funext g
    exact Ad_eq_modelTangentAd (I := I) (G := G) g Y
  have hL : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, LeftInvariantDerivation I G) ∞ L :=
    eIso.symm.toContinuousLinearEquiv.contDiff.contMDiff
  -- Factor the adjoint orbit as the inverse model isometry after the tangent adjoint orbit, then
  -- apply the chain rule and identify the tangent differential and transported bracket.
  rw [← mvfderiv_apply_eq_mfderiv_apply]
  -- Rewrite the function in `mvfderiv` form: unlike `mfderiv`, its result type is not indexed by
  -- the function's value at the base point.
  rw [hEq]
  -- The public statement uses the simp-normal linear equivalence; recover the Lie-equivalence
  -- presentation internally for the bracket-preserving transport proof.
  rw [← leftInvariantDerivationEquivGroupLieAlgebra_apply
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint X]
  rw [← leftInvariantDerivationLieEquivGroupLieAlgebra_apply
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint X]
  rw [mvfderiv_apply_eq_mfderiv_apply]
  rw [mfderiv_comp_apply (1 : G)
    (hL.mdifferentiable (by simp) (T 1))
    (hT.mdifferentiable (by simp) 1) (eLie X)]
  have hLmf :=
    (eIso.symm.toContinuousLinearEquiv.hasFDerivAt (x := T 1)).hasMFDerivAt
  rw [hLmf.mfderiv]
  simp only [L, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  have hTangent := mvfderiv_tangentAd_apply_one (I := I) (G := G) (eLie X)
    ((eIso Y : E) : GroupLieAlgebra I G)
  rw [mvfderiv_apply_eq_mfderiv_apply] at hTangent
  rw [hTangent]
  simp only [LieAlgebra.ad_apply]
  -- `GroupLieAlgebra I G` is definitionally `E`; this ascription exposes the tangent bracket to
  -- the canonical derivation/model equivalence.
  have heIsoLieY : ((eIso Y : E) : GroupLieAlgebra I G) = eLie Y := by
    exact leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply_eq_lieEquiv_apply
      (I := I) (G := G) Y
  rw [heIsoLieY]
  exact modelBracketTransport (I := I) (G := G) X Y

/-- The differential at the identity of the bounded-operator-valued adjoint representation is
Mathlib's Lie-algebra adjoint map. -/
@[simp]
theorem mfderiv_continuousAdjointRepresentation_one (X : LeftInvariantDerivation I G) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
      finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
    (show LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G from
      mfderiv I
        𝓘(ℝ, LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G)
        (continuousAdjointRepresentation (I := I) (G := G)) 1
        (pointDerivationEquivTangentSpace (I := I) 1
          BoundarylessManifold.isInteriorPoint (LeftInvariantDerivation.evalAt 1 X))) =
      LinearMap.toContinuousLinearMap
        (LieAlgebra.ad ℝ (LeftInvariantDerivation I G) X) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  -- Identify the operator-valued derivative pointwise by differentiating evaluation at `Y`.
  apply ContinuousLinearMap.ext
  intro Y
  rw [mfderiv_continuousLinearMap_apply
    (hf := (contMDiff_continuousAdjointRepresentation (I := I) (G := G)).mdifferentiable
      (by simp) 1)]
  rw [show (fun g : G => continuousAdjointRepresentation (I := I) g Y) =
      fun g : G => Ad (I := I) g Y by
    funext g
    exact continuousAdjointRepresentation_apply (I := I) g Y]
  rw [LinearMap.coe_toContinuousLinearMap']
  have h := mfderiv_Ad_apply_one (I := I) (G := G) X Y
  dsimp only at h
  exact h

end TauCeti.Lie
