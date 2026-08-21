/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Lie.Basic
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
* Sébastien Gouëzel's `Mathlib.Geometry.Manifold.GroupLieAlgebra`, especially
  `inverse_mfderiv_mul_left`, `mpullback_mulInvariantVectorField`, and
  `mulInvariantVector_mlieBracket`; the corresponding conjugation arguments below adapt the
  derivative-inverse and pullback/bracket proof patterns developed there.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

section Differential

variable [LieGroup I 1 G]

local instance lieGroupMinSmoothnessOne : LieGroup I (minSmoothness ℝ 1) G := by
  simpa using (inferInstance : LieGroup I 1 G)

/-- The continuous linear equivalence given by the differential of conjugation at the identity. -/
def adjointContinuousLinearEquiv (g : G) :
    GroupLieAlgebra I G ≃L[ℝ] GroupLieAlgebra I G :=
  (conjDiffeomorph (I := I) (n := 1) g).mfderivToContinuousLinearEquiv (by simp) 1

@[simp]
theorem adjointContinuousLinearEquiv_coe (g : G) :
    (adjointContinuousLinearEquiv (I := I) g :
      GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G) =
        mfderiv I I (conjDiffeomorph (I := I) (n := 1) g) 1 := by
  exact Diffeomorph.mfderivToContinuousLinearEquiv_coe _ _

/-- The continuous linear map underlying the differential of conjugation at the identity. -/
def adjointContinuousLinearMap (g : G) :
    GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G :=
  adjointContinuousLinearEquiv (I := I) g

@[simp]
theorem adjointContinuousLinearMap_apply (g : G) (X : GroupLieAlgebra I G) :
    adjointContinuousLinearMap (I := I) g X =
      mfderiv I I (conjDiffeomorph (I := I) (n := 1) g) 1 X := by
  congr 1
  exact adjointContinuousLinearEquiv_coe (I := I) g

@[simp]
theorem adjointContinuousLinearMap_one :
    adjointContinuousLinearMap (I := I) (1 : G) =
      ContinuousLinearMap.id ℝ (GroupLieAlgebra I G) := by
  rw [adjointContinuousLinearMap]
  rw [adjointContinuousLinearEquiv_coe]
  -- `GroupLieAlgebra I G` is the tangent model space `E`; expose it for `mfderiv_id`.
  change @Eq (E →L[ℝ] E) _ _
  rw [← mfderiv_id]
  apply mfderiv_congr
  have h := congrArg
    (fun f : TauCeti.Diff I G 1 ↦ (f : G → G))
    (map_one (conj (I := I) (n := 1)))
  simpa only [conj_apply, TauCeti.Diffeomorph.coe_one] using h

@[simp]
theorem adjointContinuousLinearMap_mul (g h : G) :
    adjointContinuousLinearMap (I := I) (g * h) =
      (adjointContinuousLinearMap (I := I) g).comp
        (adjointContinuousLinearMap (I := I) h) := by
  simp only [adjointContinuousLinearMap, adjointContinuousLinearEquiv_coe]
  -- The tangent fibers in this model-with-corners presentation share the model space `E`.
  change @Eq (E →L[ℝ] E) _ _
  have hfun :
      conjDiffeomorph (I := I) (n := 1) (g * h) =
        (conjDiffeomorph (I := I) (n := 1) g) ∘
          (conjDiffeomorph (I := I) (n := 1) h) := by
    have hmap := congrArg
      (fun f : TauCeti.Diff I G 1 ↦ (f : G → G))
      (map_mul (conj (I := I) (n := 1)) g h)
    simpa only [conj_apply, TauCeti.Diffeomorph.coe_mul] using hmap
  rw [mfderiv_congr (I := I) (I' := I) hfun]
  rw [mfderiv_comp (I := I) (I' := I) (I'' := I) _
    (((conjDiffeomorph (I := I) (n := 1) g).mdifferentiable (by simp)) _)
    (((conjDiffeomorph (I := I) (n := 1) h).mdifferentiable (by simp)) _)]
  rw [mfderiv_congr_point (I := I) (I' := I)
    (f := conjDiffeomorph (I := I) (n := 1) g)
    (x := conjDiffeomorph (I := I) (n := 1) h 1) (x' := 1)
    (by simp)]
  rfl

@[simp]
private theorem conjDiffeomorph_inv (g : G) :
    conjDiffeomorph (I := I) (n := 1) g⁻¹ =
      (conjDiffeomorph (I := I) (n := 1) g).symm := by
  have h := map_inv (conj (I := I) (n := 1)) g
  simpa only [conj_apply, TauCeti.Diffeomorph.inv_def] using h

/-- The inverse of the derivative of conjugation by `g` is the derivative of conjugation by
`g⁻¹` at the conjugated point. -/
theorem inverse_mfderiv_conjugation (g x : G) :
    (mfderiv I I (conjDiffeomorph (I := I) (n := 1) g) x).inverse =
      mfderiv I I (conjDiffeomorph (I := I) (n := 1) g⁻¹)
        (conjDiffeomorph (I := I) (n := 1) g x) := by
  rw [conjDiffeomorph_inv]
  let Φ := conjDiffeomorph (I := I) (n := 1) g
  let hΦ := Φ.isLocalDiffeomorph x
  -- Unfold the local names so Mathlib's differential-equivalence API sees the same diffeomorphism.
  change (mfderiv I I Φ x).inverse = mfderiv I I Φ.symm (Φ x)
  rw [← hΦ.mfderivToContinuousLinearEquiv_coe (by simp)]
  rw [ContinuousLinearMap.inverse_equiv]
  have heq : hΦ.localInverse =ᶠ[nhds (Φ x)] ⇑Φ.symm := by
    filter_upwards [hΦ.localInverse_eventuallyEq_right] with y hy
    apply Φ.injective
    simpa using hy
  -- The inverse field of Mathlib's packaged differential equivalence is the chosen local inverse.
  change mfderiv I I hΦ.localInverse (Φ x) = mfderiv I I Φ.symm (Φ x)
  exact Filter.EventuallyEq.mfderiv_eq (I := I) (I' := I) heq

/-- The derivative of conjugation by `g` transports a left-invariant vector field to the field
whose value at the identity is the adjoint image. -/
theorem mfderiv_conjugation_mulInvariantVectorField (g x : G)
    (X : GroupLieAlgebra I G) :
    mfderiv I I (conjDiffeomorph (I := I) (n := 1) g) x
        (mulInvariantVectorField X x) =
      mulInvariantVectorField (adjointContinuousLinearMap (I := I) g X)
        (conjDiffeomorph (I := I) (n := 1) g x) := by
  simp only [mulInvariantVectorField]
  have hreg : minSmoothness ℝ 1 ≠ 0 :=
    (lt_of_lt_of_le (by simp) le_minSmoothness).ne'
  have hfun :
      (conjDiffeomorph (I := I) (n := 1) g) ∘ (fun y : G ↦ x * y) =
        (fun y : G ↦ conjDiffeomorph (I := I) (n := 1) g x * y) ∘
          (conjDiffeomorph (I := I) (n := 1) g) := by
    funext y
    simp [Function.comp_apply, mul_assoc]
  have h := congrArg (fun f : G → G ↦ mfderiv I I f 1 X) hfun
  rw [mfderiv_comp_apply (I := I) (I' := I) (I'' := I),
    mfderiv_comp_apply (I := I) (I' := I) (I'' := I)] at h
  · rw [mfderiv_congr_point (I := I) (I' := I) (f := conjDiffeomorph (I := I) (n := 1) g)
      (x := x * 1) (x' := x) (by simp)] at h
    rw [mfderiv_congr_point (I := I) (I' := I)
      (f := fun y : G ↦ conjDiffeomorph (I := I) (n := 1) g x * y)
      (x := conjDiffeomorph (I := I) (n := 1) g 1) (x' := 1)
      (by simp)] at h
    -- For this model-with-corners presentation, each tangent fiber is implemented by `E`.
    change @Eq E _ _
    rw [adjointContinuousLinearMap_apply]
    exact h
  · exact contMDiffAt_mul_left.mdifferentiableAt hreg
  · exact ((conjDiffeomorph (I := I) (n := 1) g).mdifferentiable (by simp)) _
  · exact ((conjDiffeomorph (I := I) (n := 1) g).mdifferentiable (by simp)) _
  · exact contMDiffAt_mul_left.mdifferentiableAt hreg

/-- Pullback through inverse conjugation is the derivative of forward conjugation. -/
theorem mpullback_conjugation (g x : G) (V : ∀ y : G, TangentSpace I y) :
    VectorField.mpullback I I (conjDiffeomorph (I := I) (n := 1) g⁻¹) V x =
      mfderiv I I (conjDiffeomorph (I := I) (n := 1) g)
        (conjDiffeomorph (I := I) (n := 1) g⁻¹ x)
        (V (conjDiffeomorph (I := I) (n := 1) g⁻¹ x)) := by
  simp only [VectorField.mpullback]
  rw [inverse_mfderiv_conjugation]
  rw [mfderiv_congr (I := I) (I' := I)
    (f := conjDiffeomorph (I := I) (n := 1) g⁻¹⁻¹)
    (f' := conjDiffeomorph (I := I) (n := 1) g) (by simp)]
  rfl

/-- Pullback by conjugation by `g⁻¹` sends the left-invariant field of `X` to the
left-invariant field of the adjoint image of `X`. -/
theorem mpullback_conjugation_mulInvariantVectorField (g : G)
    (X : GroupLieAlgebra I G) :
    VectorField.mpullback I I (conjDiffeomorph (I := I) (n := 1) g⁻¹)
        (mulInvariantVectorField X) =
      mulInvariantVectorField (adjointContinuousLinearMap (I := I) g X) := by
  funext x
  rw [mpullback_conjugation]
  have hpush := mfderiv_conjugation_mulInvariantVectorField (I := I) g
    (conjDiffeomorph (I := I) (n := 1) g⁻¹ x) X
  have hpoint : conjDiffeomorph (I := I) (n := 1) g
      (conjDiffeomorph (I := I) (n := 1) g⁻¹ x) = x := by
    rw [conjDiffeomorph_inv]
    exact (conjDiffeomorph (I := I) (n := 1) g).apply_symm_apply x
  rw [hpoint] at hpush
  exact hpush

/-- At the identity, pullback by conjugation by `g⁻¹` is the adjoint differential of `g`. -/
theorem mpullback_conjugation_one (g : G) (V : ∀ x : G, TangentSpace I x) :
    VectorField.mpullback I I (conjDiffeomorph (I := I) (n := 1) g⁻¹) V 1 =
      adjointContinuousLinearMap (I := I) g (V 1) := by
  rw [mpullback_conjugation]
  rw [mfderiv_congr_point (I := I) (I' := I)
    (f := conjDiffeomorph (I := I) (n := 1) g)
    (x := conjDiffeomorph (I := I) (n := 1) g⁻¹ 1) (x' := 1)
    (by simp)]
  rw [adjointContinuousLinearMap_apply]
  have hpoint : conjDiffeomorph (I := I) (n := 1) g⁻¹ 1 = 1 := by
    simp only [conjDiffeomorph_apply, mul_one, inv_inv, inv_mul_cancel]
  exact congrArg (fun y : G ↦ mfderiv I I
    (conjDiffeomorph (I := I) (n := 1) g) 1 (V y)) hpoint

end Differential

section Bracket

variable [LieGroup I 3 G]

attribute [local instance] LieGroup.minSmoothnessThree

local instance lieGroupOne : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := 3) (by norm_num)

/-- The differential of conjugation preserves the manifold Lie bracket. -/
theorem adjointContinuousLinearMap_lie [CompleteSpace E] (g : G)
    (X Y : GroupLieAlgebra I G) :
    adjointContinuousLinearMap (I := I) g ⁅X, Y⁆ =
      ⁅adjointContinuousLinearMap (I := I) g X,
        adjointContinuousLinearMap (I := I) g Y⁆ := by
  have h := VectorField.mpullback_mlieBracket
    (I := I) (I' := I) (n := 3)
    (f := conjDiffeomorph (I := I) (n := 3) g⁻¹)
    (V := mulInvariantVectorField X) (W := mulInvariantVectorField Y) (x₀ := (1 : G))
    (mdifferentiableAt_mulInvariantVectorField X)
    (mdifferentiableAt_mulInvariantVectorField Y)
    (conjDiffeomorph (I := I) (n := 3) g⁻¹).contMDiffAt
      (by norm_num)
  have hconj :
      (conjDiffeomorph (I := I) (n := 3) g⁻¹ : G → G) =
        (conjDiffeomorph (I := I) (n := 1) g⁻¹ : G → G) := by
    funext x
    simp only [conjDiffeomorph_apply]
  rw [hconj] at h
  rw [mpullback_conjugation_mulInvariantVectorField,
    mpullback_conjugation_mulInvariantVectorField] at h
  rw [mpullback_conjugation_one] at h
  exact h

/-- The group adjoint automorphism: the differential at the identity of conjugation by `g`. -/
def tangentAd [CompleteSpace E] (g : G) :
    GroupLieAlgebra I G ≃ₗ⁅ℝ⁆ GroupLieAlgebra I G where
  toFun := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv
  invFun := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv.symm
  left_inv := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv.left_inv
  right_inv := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv.right_inv
  map_add' := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv.map_add
  map_smul' := (adjointContinuousLinearEquiv (I := I) g).toLinearEquiv.map_smul
  map_lie' := by
    intro X Y
    exact adjointContinuousLinearMap_lie (I := I) g X Y

@[simp]
theorem tangentAd_apply [CompleteSpace E] (g : G) (X : GroupLieAlgebra I G) :
    tangentAd (I := I) g X = adjointContinuousLinearMap (I := I) g X :=
  (rfl)

/-- The tangent adjoint automorphism at the identity is the identity Lie equivalence. -/
@[simp]
theorem tangentAd_one [CompleteSpace E] :
    tangentAd (I := I) (1 : G) = LieEquiv.refl := by
  ext X
  simp [tangentAd_apply]

/-- The tangent adjoint action sends a product to the composite of the two adjoint maps. -/
@[simp]
theorem tangentAd_mul [CompleteSpace E] (g h : G) :
    tangentAd (I := I) (g * h) =
      (tangentAd (I := I) h).trans (tangentAd (I := I) g) := by
  ext X
  rw [tangentAd_apply, LieEquiv.trans_apply, tangentAd_apply, tangentAd_apply]
  exact congrArg
    (fun f : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G ↦ f X)
    (adjointContinuousLinearMap_mul (I := I) g h)

/-- The tangent adjoint automorphism of `g⁻¹` is the inverse of that of `g`. -/
@[simp]
theorem tangentAd_inv [CompleteSpace E] (g : G) :
    tangentAd (I := I) g⁻¹ = (tangentAd (I := I) g).symm := by
  ext X
  apply (tangentAd (I := I) g).injective
  -- Expose the coercions and symmetry of `LieEquiv` so injectivity can use the product law.
  change tangentAd (I := I) g (tangentAd (I := I) g⁻¹ X) =
    tangentAd (I := I) g ((tangentAd (I := I) g).symm X)
  rw [LieEquiv.apply_symm_apply]
  have h := congrArg
    (fun e : GroupLieAlgebra I G ≃ₗ⁅ℝ⁆ GroupLieAlgebra I G ↦ e X)
    (tangentAd_mul (I := I) g g⁻¹)
  simpa using h.symm

end Bracket

end TauCeti.Lie
