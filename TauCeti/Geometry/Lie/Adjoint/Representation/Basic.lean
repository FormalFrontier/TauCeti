/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.Adjoint.Smooth
public import TauCeti.RepresentationTheory.Continuous.Transport

/-!
# The group adjoint representation

This file bundles the roadmap-facing group adjoint `Ad` as a continuous representation on
left-invariant derivations. It transports operator-valued smoothness across the canonical
isometric identification between left-invariant derivations and the tangent space at the identity,
then derives joint smoothness of the action by evaluation.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `TauCeti.Lie.continuousAdjointRepresentation`: the group adjoint as a continuous representation.

## Main results

* `TauCeti.Lie.contMDiff_Ad_apply`: the joint action `(g, X) ↦ Ad g X` is smooth.
* `TauCeti.Lie.contMDiff_continuousAdjointRepresentation`: the bounded-operator-valued
  representation is smooth.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothnessThree

local instance : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

private noncomputable def derivationModelEquiv :
    LeftInvariantDerivation I G ≃L[ℝ] E :=
  (leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)).toContinuousLinearEquiv

private noncomputable def modelAdjointRepresentation : ContRepresentation ℝ G E :=
  .ofMonoidHom
    { toFun := fun g ↦ show E →L[ℝ] E from adjointContinuousLinearMap (I := I) g
      map_one' := by
        -- `GroupLieAlgebra I G` is definitionally `E`; expose both it and the operator-space unit.
        change (adjointContinuousLinearMap (I := I) (1 : G) : E →L[ℝ] E) =
          ContinuousLinearMap.id ℝ E
        exact adjointContinuousLinearMap_one (I := I) (G := G)
      map_mul' := by
        intro g h
        -- `GroupLieAlgebra I G` is definitionally the model space `E`; expose it before using the
        -- operator-composition form of the adjoint multiplication law.
        change (adjointContinuousLinearMap (I := I) (g * h) : E →L[ℝ] E) =
          (adjointContinuousLinearMap (I := I) g).comp
            (adjointContinuousLinearMap (I := I) h)
        exact adjointContinuousLinearMap_mul (I := I) g h }

/-- The adjoint representation valued in bounded operators. -/
def continuousAdjointRepresentation : ContRepresentation ℝ G (LeftInvariantDerivation I G) :=
  TauCeti.ContRepresentation.congr (derivationModelEquiv (I := I) (G := G)).symm
    (modelAdjointRepresentation (I := I) (G := G))

private theorem continuousAdjointRepresentation_coe :
    ⇑(continuousAdjointRepresentation (I := I) (G := G)) = fun g ↦
      (derivationModelEquiv (I := I) (G := G)).symm.conjContinuousAlgEquiv
        (show E →L[ℝ] E from adjointContinuousLinearMap (I := I) g) :=
  by
    rw [continuousAdjointRepresentation, TauCeti.ContRepresentation.coe_congr,
      modelAdjointRepresentation]
    rfl

/-- The packaged continuous adjoint representation acts by the derivation adjoint action. -/
@[simp]
theorem continuousAdjointRepresentation_apply (g : G) (D : LeftInvariantDerivation I G) :
    continuousAdjointRepresentation (I := I) g D = Ad (I := I) g D := by
  rw [continuousAdjointRepresentation, TauCeti.ContRepresentation.congr_apply]
  apply (derivationModelEquiv (I := I) (G := G)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  -- `GroupLieAlgebra I G` is definitionally `E`; expose the conjugated model-space operator.
  change (adjointContinuousLinearMap (I := I) g : E →L[ℝ] E)
      (derivationModelEquiv (I := I) (G := G) D) =
    derivationModelEquiv (I := I) (G := G) (Ad (I := I) g D)
  dsimp only [derivationModelEquiv]
  -- The tangent adjoint is stated on `GroupLieAlgebra I G`, definitionally the model space `E`;
  -- cast its equation back to `E` to compose it with the isometric intertwining identity.
  have htangent := tangentAd_apply (I := I) g
    ((leftInvariantDerivationLinearIsometryEquivModelVectorSpace
      (I := I) (G := G) D : E) : GroupLieAlgebra I G)
  have htangentE := congrArg (fun X : GroupLieAlgebra I G ↦ show E from X) htangent
  have h := leftInvariantDerivationLinearIsometryEquivModelVectorSpace_Ad (I := I) g D
  dsimp only at h
  exact htangentE.symm.trans h.symm

/-- The bounded-operator-valued adjoint representation is smooth. -/
theorem contMDiff_continuousAdjointRepresentation :
    ContMDiff I
      𝓘(ℝ, LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G) ∞
      (continuousAdjointRepresentation (I := I) (G := G)) := by
  rw [continuousAdjointRepresentation_coe]
  exact (derivationModelEquiv (I := I) (G := G)).symm.conjContinuousAlgEquiv
    |>.toContinuousLinearEquiv.contDiff.contMDiff.comp
    (contMDiff_adjointContinuousLinearMap (I := I) (G := G))

/-- The group adjoint action on left-invariant derivations is jointly smooth. -/
theorem contMDiff_Ad_apply :
    ContMDiff (I.prod 𝓘(ℝ, LeftInvariantDerivation I G))
      𝓘(ℝ, LeftInvariantDerivation I G) ∞
      (fun p : G × LeftInvariantDerivation I G ↦ Ad (I := I) p.1 p.2) := by
  rw [show (fun p : G × LeftInvariantDerivation I G ↦ Ad (I := I) p.1 p.2) =
      fun p ↦ continuousAdjointRepresentation (I := I) p.1 p.2 by
    funext p
    exact (continuousAdjointRepresentation_apply (I := I) p.1 p.2).symm]
  exact ((contMDiff_continuousAdjointRepresentation (I := I) (G := G)).comp
    contMDiff_fst).clm_apply contMDiff_snd

end TauCeti.Lie
