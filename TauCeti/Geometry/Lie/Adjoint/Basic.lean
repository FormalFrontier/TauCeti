/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import TauCeti.Geometry.Lie.Adjoint.Conjugation

/-!
# The tangent-space adjoint action of a Lie group

The tangent-space adjoint action is the differential at the identity of conjugation. We first prove
that this differential transports left-invariant vector fields. Naturality of the manifold Lie
bracket then shows that it is a Lie algebra automorphism, and the composition law for conjugation
gives the representation law. A subsequent file transports this construction to the roadmap-facing
Lie algebra of left-invariant derivations.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `TauCeti.Lie.tangentAd`: the resulting tangent Lie algebra automorphism.

## Main results

* `TauCeti.Lie.adjointContinuousLinearMap_lie`: the differential preserves the Lie bracket.
* `TauCeti.Lie.tangentAd_mul`: the tangent adjoint automorphism respects group multiplication.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

local instance lieGroupMinSmoothnessThree : LieGroup I (minSmoothness ℝ 3) G :=
  LieGroup.of_le (I := I) (G := G) (m := minSmoothness ℝ 3) (n := ∞)
    (by simpa using (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out)

/-- The continuous linear map underlying the differential of conjugation at the identity. -/
def adjointContinuousLinearMap (g : G) :
    GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G :=
  mfderiv I I (conjDiffeomorph (I := I) (n := ∞) g) 1

@[simp]
theorem adjointContinuousLinearMap_apply (g : G) (X : GroupLieAlgebra I G) :
    adjointContinuousLinearMap (I := I) g X =
      mfderiv I I (conjDiffeomorph (I := I) (n := ∞) g) 1 X :=
  (rfl)

@[simp]
theorem adjointContinuousLinearMap_one :
    adjointContinuousLinearMap (I := I) (1 : G) =
      ContinuousLinearMap.id ℝ (GroupLieAlgebra I G) := by
  change @Eq (E →L[ℝ] E) _ _
  rw [← mfderiv_id]
  apply mfderiv_congr
  funext x
  simp

theorem adjointContinuousLinearMap_mul (g h : G) :
    adjointContinuousLinearMap (I := I) (g * h) =
      (adjointContinuousLinearMap (I := I) g).comp
        (adjointContinuousLinearMap (I := I) h) := by
  unfold adjointContinuousLinearMap
  change @Eq (E →L[ℝ] E) _ _
  have hfun :
      conjDiffeomorph (I := I) (n := ∞) (g * h) =
        (conjDiffeomorph (I := I) (n := ∞) g) ∘
          (conjDiffeomorph (I := I) (n := ∞) h) := by
    funext x
    simp only [conjDiffeomorph_apply, Function.comp_apply]
    group
  rw [mfderiv_congr (I := I) (I' := I) hfun]
  rw [mfderiv_comp (I := I) (I' := I) (I'' := I) _
    (((conjDiffeomorph (I := I) (n := ∞) g).mdifferentiable (by simp)) _)
    (((conjDiffeomorph (I := I) (n := ∞) h).mdifferentiable (by simp)) _)]
  rw [mfderiv_congr_point (I := I) (I' := I)
    (f := conjDiffeomorph (I := I) (n := ∞) g)
    (x := conjDiffeomorph (I := I) (n := ∞) h 1) (x' := 1)
    (by simp)]
  with_unfolding_all rfl

theorem inverse_mfderiv_conjugation (g x : G) :
    (mfderiv I I (conjDiffeomorph (I := I) (n := ∞) g) x).inverse =
      mfderiv I I (conjDiffeomorph (I := I) (n := ∞) g⁻¹)
        (conjDiffeomorph (I := I) (n := ∞) g x) := by
  have hdiff (a : G) : MDifferentiableAt I I (conjDiffeomorph (I := I) (n := ∞) a) x :=
    ((conjDiffeomorph (I := I) (n := ∞) a).mdifferentiable (by simp)) x
  have A : mfderiv I I
      ((conjDiffeomorph (I := I) (n := ∞) g⁻¹) ∘
        (conjDiffeomorph (I := I) (n := ∞) g)) x =
        ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    have h :
        (conjDiffeomorph (I := I) (n := ∞) g⁻¹) ∘
          (conjDiffeomorph (I := I) (n := ∞) g) = id := by
      funext y
      simp [Function.comp_apply, mul_assoc]
    rw [h, mfderiv_id]
  rw [mfderiv_comp (I := I) (I' := I) (I'' := I) _
    (((conjDiffeomorph (I := I) (n := ∞) g⁻¹).mdifferentiable (by simp)) _)
    (hdiff g)] at A
  have A' : mfderiv I I
      ((conjDiffeomorph (I := I) (n := ∞) g) ∘
        (conjDiffeomorph (I := I) (n := ∞) g⁻¹))
        (conjDiffeomorph (I := I) (n := ∞) g x) =
        ContinuousLinearMap.id ℝ
          (TangentSpace I (conjDiffeomorph (I := I) (n := ∞) g x)) := by
    have h :
        (conjDiffeomorph (I := I) (n := ∞) g) ∘
          (conjDiffeomorph (I := I) (n := ∞) g⁻¹) = id := by
      funext y
      simp [Function.comp_apply, mul_assoc]
    rw [h, mfderiv_id]
  rw [mfderiv_comp (I := I) (I' := I) (I'' := I) _
    (((conjDiffeomorph (I := I) (n := ∞) g).mdifferentiable (by simp)) _)
    (((conjDiffeomorph (I := I) (n := ∞) g⁻¹).mdifferentiable (by simp)) _)] at A'
  rw [mfderiv_congr_point (I := I) (I' := I)
    (f := conjDiffeomorph (I := I) (n := ∞) g)
    (x := conjDiffeomorph (I := I) (n := ∞) g⁻¹
      (conjDiffeomorph (I := I) (n := ∞) g x))
    (x' := x) (by simp only [conjDiffeomorph_apply]; group)] at A'
  exact ContinuousLinearMap.inverse_eq A' A

theorem mfderiv_conjugation_mulInvariantVectorField (g x : G)
    (X : GroupLieAlgebra I G) :
    mfderiv I I (conjDiffeomorph (I := I) (n := ∞) g) x
        (mulInvariantVectorField X x) =
      mulInvariantVectorField (adjointContinuousLinearMap (I := I) g X)
        (conjDiffeomorph (I := I) (n := ∞) g x) := by
  simp only [mulInvariantVectorField]
  have hfun :
      (conjDiffeomorph (I := I) (n := ∞) g) ∘ (fun y : G ↦ x * y) =
        (fun y : G ↦ conjDiffeomorph (I := I) (n := ∞) g x * y) ∘
          (conjDiffeomorph (I := I) (n := ∞) g) := by
    funext y
    simp [Function.comp_apply, mul_assoc]
  have h := congrArg (fun f : G → G ↦ mfderiv I I f 1 X) hfun
  rw [mfderiv_comp_apply (I := I) (I' := I) (I'' := I),
    mfderiv_comp_apply (I := I) (I' := I) (I'' := I)] at h
  · rw [mfderiv_congr_point (I := I) (I' := I) (f := conjDiffeomorph (I := I) (n := ∞) g)
      (x := x * 1) (x' := x) (by simp)] at h
    rw [mfderiv_congr_point (I := I) (I' := I)
      (f := fun y : G ↦ conjDiffeomorph (I := I) (n := ∞) g x * y)
      (x := conjDiffeomorph (I := I) (n := ∞) g 1) (x' := 1)
      (by simp)] at h
    change @Eq E _ _
    exact h
  · exact contMDiffAt_mul_left.mdifferentiableAt one_ne_zero
  · exact ((conjDiffeomorph (I := I) (n := ∞) g).mdifferentiable (by simp)) _
  · exact ((conjDiffeomorph (I := I) (n := ∞) g).mdifferentiable (by simp)) _
  · exact contMDiffAt_mul_left.mdifferentiableAt one_ne_zero

theorem mpullback_conjugation_mulInvariantVectorField (g : G)
    (X : GroupLieAlgebra I G) :
    VectorField.mpullback I I (conjDiffeomorph (I := I) (n := ∞) g⁻¹)
        (mulInvariantVectorField X) =
      mulInvariantVectorField (adjointContinuousLinearMap (I := I) g X) := by
  funext x
  simp only [VectorField.mpullback]
  rw [inverse_mfderiv_conjugation]
  rw [mfderiv_congr (I := I) (I' := I)
    (f := conjDiffeomorph (I := I) (n := ∞) g⁻¹⁻¹)
    (f' := conjDiffeomorph (I := I) (n := ∞) g) (by simp)]
  have hpush := mfderiv_conjugation_mulInvariantVectorField (I := I) g
    (conjDiffeomorph (I := I) (n := ∞) g⁻¹ x) X
  change @Eq E _ _
  change @Eq E _ _ at hpush
  have hpoint : conjDiffeomorph (I := I) (n := ∞) g
      (conjDiffeomorph (I := I) (n := ∞) g⁻¹ x) = x := by
    simp only [conjDiffeomorph_apply]
    group
  rw [hpoint] at hpush
  exact hpush

theorem mpullback_conjugation_one (g : G) (V : ∀ x : G, TangentSpace I x) :
    VectorField.mpullback I I (conjDiffeomorph (I := I) (n := ∞) g⁻¹) V 1 =
      adjointContinuousLinearMap (I := I) g (V 1) := by
  simp only [VectorField.mpullback]
  rw [inverse_mfderiv_conjugation]
  rw [mfderiv_congr (I := I) (I' := I)
    (f := conjDiffeomorph (I := I) (n := ∞) g⁻¹⁻¹)
    (f' := conjDiffeomorph (I := I) (n := ∞) g) (by simp)]
  rw [mfderiv_congr_point (I := I) (I' := I)
    (f := conjDiffeomorph (I := I) (n := ∞) g)
    (x := conjDiffeomorph (I := I) (n := ∞) g⁻¹ 1) (x' := 1)
    (by simp)]
  change @Eq E _ _
  rw [adjointContinuousLinearMap]
  congr 1
  exact congrArg (fun y : G ↦ (V y : E)) (by simp)

theorem adjointContinuousLinearMap_lie [CompleteSpace E] (g : G)
    (X Y : GroupLieAlgebra I G) :
    adjointContinuousLinearMap (I := I) g ⁅X, Y⁆ =
      ⁅adjointContinuousLinearMap (I := I) g X,
        adjointContinuousLinearMap (I := I) g Y⁆ := by
  have h := VectorField.mpullback_mlieBracket
    (I := I) (I' := I) (n := ∞)
    (f := conjDiffeomorph (I := I) (n := ∞) g⁻¹)
    (V := mulInvariantVectorField X) (W := mulInvariantVectorField Y) (x₀ := (1 : G))
    (mdifferentiableAt_mulInvariantVectorField X)
    (mdifferentiableAt_mulInvariantVectorField Y)
    (conjDiffeomorph (I := I) (n := ∞) g⁻¹).contMDiffAt
      (by simpa using (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out)
  rw [mpullback_conjugation_mulInvariantVectorField,
    mpullback_conjugation_mulInvariantVectorField] at h
  rw [mpullback_conjugation_one] at h
  exact h

/-- The group adjoint automorphism: the differential at the identity of conjugation by `g`. -/
def tangentAd [CompleteSpace E] (g : G) :
    GroupLieAlgebra I G ≃ₗ⁅ℝ⁆ GroupLieAlgebra I G where
  toFun := adjointContinuousLinearMap (I := I) g
  invFun := adjointContinuousLinearMap (I := I) g⁻¹
  left_inv X := by
    have h := congrArg (fun f : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G ↦ f X)
      (adjointContinuousLinearMap_mul (I := I) g⁻¹ g)
    simpa using h.symm
  right_inv X := by
    have h := congrArg (fun f : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G ↦ f X)
      (adjointContinuousLinearMap_mul (I := I) g g⁻¹)
    simpa using h.symm
  map_add' := map_add _
  map_smul' := map_smul _
  map_lie' := by
    intro X Y
    exact adjointContinuousLinearMap_lie (I := I) g X Y

@[simp]
theorem tangentAd_apply [CompleteSpace E] (g : G) (X : GroupLieAlgebra I G) :
    tangentAd (I := I) g X = adjointContinuousLinearMap (I := I) g X :=
  (rfl)

@[simp]
theorem tangentAd_one [CompleteSpace E] :
    tangentAd (I := I) (1 : G) = LieEquiv.refl := by
  ext X
  simp [tangentAd_apply]

theorem tangentAd_mul [CompleteSpace E] (g h : G) :
    tangentAd (I := I) (g * h) =
      (tangentAd (I := I) h).trans (tangentAd (I := I) g) := by
  ext X
  rw [tangentAd_apply, LieEquiv.trans_apply, tangentAd_apply, tangentAd_apply]
  exact congrArg
    (fun f : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G ↦ f X)
    (adjointContinuousLinearMap_mul (I := I) g h)

@[simp]
theorem tangentAd_inv [CompleteSpace E] (g : G) :
    tangentAd (I := I) g⁻¹ = (tangentAd (I := I) g).symm := by
  ext X
  rfl

end TauCeti.Lie
