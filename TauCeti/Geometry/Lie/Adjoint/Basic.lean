/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Lie.Adjoint.Conjugation

/-!
# The adjoint action of a Lie group

The group adjoint action is the differential at the identity of conjugation.  We first prove that
this differential transports left-invariant vector fields.  Naturality of the manifold Lie
bracket then shows that it is a Lie algebra automorphism, and the composition law for conjugation
gives the representation law.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `TauCeti.Lie.adjointContinuousLinearMap`: the differential of conjugation at the identity.
* `TauCeti.Lie.Ad`: the resulting Lie algebra automorphism.

## Main results

* `TauCeti.Lie.adjointContinuousLinearMap_lie`: the differential preserves the Lie bracket.
* `TauCeti.Lie.Ad_mul`: the adjoint automorphism respects group multiplication.
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

/-- The differential at the identity of conjugation by `g`, as a continuous linear
equivalence of the tangent Lie algebra.  The fixed-point identity
`conjugationDiffeomorph_one` identifies the target fiber of the differential with the tangent
space at the identity. -/
@[expose]
def adjointContinuousLinearEquiv (g : G) :
    GroupLieAlgebra I G ≃L[ℝ] GroupLieAlgebra I G :=
  conjugationDiffeomorph_one (I := I) g ▸
    (conjugationDiffeomorph (I := I) g).mfderivToContinuousLinearEquiv (by simp) (1 : G)

/-- The continuous linear map underlying the differential of conjugation at the identity. -/
@[expose]
def adjointContinuousLinearMap (g : G) :
    GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G :=
  mfderiv I I (conjugationDiffeomorph (I := I) g) 1

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem adjointContinuousLinearMap_one :
    adjointContinuousLinearMap (I := I) (1 : G) =
      ContinuousLinearMap.id ℝ (GroupLieAlgebra I G) := by
  change @Eq (E →L[ℝ] E) _ _
  rw [← mfderiv_id]
  apply mfderiv_congr
  funext x
  simp

set_option backward.isDefEq.respectTransparency false in
theorem adjointContinuousLinearMap_mul (g h : G) :
    adjointContinuousLinearMap (I := I) (g * h) =
      (adjointContinuousLinearMap (I := I) g).comp
        (adjointContinuousLinearMap (I := I) h) := by
  unfold adjointContinuousLinearMap
  change @Eq (E →L[ℝ] E) _ _
  have hfun :
      conjugationDiffeomorph (I := I) (g * h) =
        (conjugationDiffeomorph (I := I) g) ∘
          (conjugationDiffeomorph (I := I) h) := by
    funext x
    simp only [conjugationDiffeomorph_apply, Function.comp_apply]
    group
  rw [mfderiv_congr (I := I) (I' := I) hfun]
  rw [mfderiv_comp (I := I) (I' := I) (I'' := I) _
    (((conjugationDiffeomorph (I := I) g).mdifferentiable (by simp)) _)
    (((conjugationDiffeomorph (I := I) h).mdifferentiable (by simp)) _)]
  rw [mfderiv_congr_point (I := I) (I' := I)
    (f := conjugationDiffeomorph (I := I) g)
    (x := conjugationDiffeomorph (I := I) h 1) (x' := 1)
    (conjugationDiffeomorph_one (I := I) h)]

set_option backward.isDefEq.respectTransparency false in
theorem inverse_mfderiv_conjugation (g x : G) :
    (mfderiv I I (conjugationDiffeomorph (I := I) g) x).inverse =
      mfderiv I I (conjugationDiffeomorph (I := I) g⁻¹)
        (conjugationDiffeomorph (I := I) g x) := by
  have hdiff (a : G) : MDifferentiableAt I I (conjugationDiffeomorph (I := I) a) x :=
    ((conjugationDiffeomorph (I := I) a).mdifferentiable (by simp)) x
  have A : mfderiv I I
      ((conjugationDiffeomorph (I := I) g⁻¹) ∘
        (conjugationDiffeomorph (I := I) g)) x =
        ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    have h :
        (conjugationDiffeomorph (I := I) g⁻¹) ∘
          (conjugationDiffeomorph (I := I) g) = id := by
      funext y
      simp [Function.comp_apply, mul_assoc]
    rw [h, mfderiv_id]
  rw [mfderiv_comp (I := I) (I' := I) (I'' := I) _
    (((conjugationDiffeomorph (I := I) g⁻¹).mdifferentiable (by simp)) _)
    (hdiff g)] at A
  have A' : mfderiv I I
      ((conjugationDiffeomorph (I := I) g) ∘
        (conjugationDiffeomorph (I := I) g⁻¹))
        (conjugationDiffeomorph (I := I) g x) =
        ContinuousLinearMap.id ℝ (TangentSpace I (conjugationDiffeomorph (I := I) g x)) := by
    have h :
        (conjugationDiffeomorph (I := I) g) ∘
          (conjugationDiffeomorph (I := I) g⁻¹) = id := by
      funext y
      simp [Function.comp_apply, mul_assoc]
    rw [h, mfderiv_id]
  rw [mfderiv_comp (I := I) (I' := I) (I'' := I) _
    (((conjugationDiffeomorph (I := I) g).mdifferentiable (by simp)) _)
    (((conjugationDiffeomorph (I := I) g⁻¹).mdifferentiable (by simp)) _)] at A'
  rw [mfderiv_congr_point (I := I) (I' := I)
    (f := conjugationDiffeomorph (I := I) g)
    (x := conjugationDiffeomorph (I := I) g⁻¹ (conjugationDiffeomorph (I := I) g x))
    (x' := x) (by simp only [conjugationDiffeomorph_apply]; group)] at A'
  exact ContinuousLinearMap.inverse_eq A' A

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_conjugation_mulInvariantVectorField (g x : G)
    (X : GroupLieAlgebra I G) :
    mfderiv I I (conjugationDiffeomorph (I := I) g) x
        (mulInvariantVectorField X x) =
      mulInvariantVectorField (adjointContinuousLinearMap (I := I) g X)
        (conjugationDiffeomorph (I := I) g x) := by
  simp only [mulInvariantVectorField]
  have hfun :
      (conjugationDiffeomorph (I := I) g) ∘ (fun y : G ↦ x * y) =
        (fun y : G ↦ conjugationDiffeomorph (I := I) g x * y) ∘
          (conjugationDiffeomorph (I := I) g) := by
    funext y
    simp [Function.comp_apply, mul_assoc]
  have h := congrArg (fun f : G → G ↦ mfderiv I I f 1 X) hfun
  rw [mfderiv_comp_apply (I := I) (I' := I) (I'' := I),
    mfderiv_comp_apply (I := I) (I' := I) (I'' := I)] at h
  · rw [mfderiv_congr_point (I := I) (I' := I) (f := conjugationDiffeomorph (I := I) g)
      (x := x * 1) (x' := x) (by simp)] at h
    rw [mfderiv_congr_point (I := I) (I' := I)
      (f := fun y : G ↦ conjugationDiffeomorph (I := I) g x * y)
      (x := conjugationDiffeomorph (I := I) g 1) (x' := 1)
      (conjugationDiffeomorph_one (I := I) g)] at h
    change @Eq E _ _
    exact h
  · exact contMDiffAt_mul_left.mdifferentiableAt one_ne_zero
  · exact ((conjugationDiffeomorph (I := I) g).mdifferentiable (by simp)) _
  · exact ((conjugationDiffeomorph (I := I) g).mdifferentiable (by simp)) _
  · exact contMDiffAt_mul_left.mdifferentiableAt one_ne_zero

set_option backward.isDefEq.respectTransparency false in
theorem mpullback_conjugation_mulInvariantVectorField (g : G)
    (X : GroupLieAlgebra I G) :
    VectorField.mpullback I I (conjugationDiffeomorph (I := I) g⁻¹)
        (mulInvariantVectorField X) =
      mulInvariantVectorField (adjointContinuousLinearMap (I := I) g X) := by
  funext x
  simp only [VectorField.mpullback]
  rw [inverse_mfderiv_conjugation]
  rw [mfderiv_congr (I := I) (I' := I)
    (f := conjugationDiffeomorph (I := I) g⁻¹⁻¹)
    (f' := conjugationDiffeomorph (I := I) g) (by simp)]
  have hpush := mfderiv_conjugation_mulInvariantVectorField (I := I) g
    (conjugationDiffeomorph (I := I) g⁻¹ x) X
  change @Eq E _ _
  change @Eq E _ _ at hpush
  calc
    _ = (mulInvariantVectorField (adjointContinuousLinearMap (I := I) g X)
          (conjugationDiffeomorph (I := I) g
            (conjugationDiffeomorph (I := I) g⁻¹ x)) : E) := hpush
    _ = (mulInvariantVectorField (adjointContinuousLinearMap (I := I) g X) x : E) :=
      congrArg (fun y : G ↦
      (mulInvariantVectorField (adjointContinuousLinearMap (I := I) g X) y : E)) (by
        simp only [conjugationDiffeomorph_apply]
        group)

set_option backward.isDefEq.respectTransparency false in
theorem mpullback_conjugation_one (g : G) (V : ∀ x : G, TangentSpace I x) :
    VectorField.mpullback I I (conjugationDiffeomorph (I := I) g⁻¹) V 1 =
      adjointContinuousLinearMap (I := I) g (V 1) := by
  simp only [VectorField.mpullback]
  rw [inverse_mfderiv_conjugation]
  rw [mfderiv_congr (I := I) (I' := I)
    (f := conjugationDiffeomorph (I := I) g⁻¹⁻¹)
    (f' := conjugationDiffeomorph (I := I) g) (by simp)]
  rw [mfderiv_congr_point (I := I) (I' := I)
    (f := conjugationDiffeomorph (I := I) g)
    (x := conjugationDiffeomorph (I := I) g⁻¹ 1) (x' := 1)
    (conjugationDiffeomorph_one (I := I) g⁻¹)]
  change @Eq E _ _
  rw [adjointContinuousLinearMap]
  congr 1
  exact congrArg (fun y : G ↦ (V y : E)) (conjugationDiffeomorph_one (I := I) g⁻¹)

set_option backward.isDefEq.respectTransparency false in
theorem adjointContinuousLinearMap_lie [CompleteSpace E] (g : G)
    (X Y : GroupLieAlgebra I G) :
    adjointContinuousLinearMap (I := I) g ⁅X, Y⁆ =
      ⁅adjointContinuousLinearMap (I := I) g X,
        adjointContinuousLinearMap (I := I) g Y⁆ := by
  have h := VectorField.mpullback_mlieBracket
    (I := I) (I' := I) (n := ∞)
    (f := conjugationDiffeomorph (I := I) g⁻¹)
    (V := mulInvariantVectorField X) (W := mulInvariantVectorField Y) (x₀ := (1 : G))
    (mdifferentiableAt_mulInvariantVectorField X)
    (mdifferentiableAt_mulInvariantVectorField Y)
    (conjugationDiffeomorph (I := I) g⁻¹).contMDiffAt
      (by simpa using (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out)
  rw [mpullback_conjugation_mulInvariantVectorField,
    mpullback_conjugation_mulInvariantVectorField] at h
  rw [mpullback_conjugation_one] at h
  exact h

/-- The group adjoint automorphism: the differential at the identity of conjugation by `g`. -/
@[expose]
def Ad [CompleteSpace E] (g : G) :
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
theorem Ad_apply [CompleteSpace E] (g : G) (X : GroupLieAlgebra I G) :
    Ad (I := I) g X = adjointContinuousLinearMap (I := I) g X :=
  rfl

@[simp]
theorem Ad_one [CompleteSpace E] :
    Ad (I := I) (1 : G) = LieEquiv.refl := by
  ext X
  simp [Ad_apply]

theorem Ad_mul [CompleteSpace E] (g h : G) :
    Ad (I := I) (g * h) = (Ad (I := I) h).trans (Ad (I := I) g) := by
  ext X
  simpa [Ad_apply] using congrArg
    (fun f : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G ↦ f X)
    (adjointContinuousLinearMap_mul (I := I) g h)

@[simp]
theorem Ad_inv [CompleteSpace E] (g : G) :
    Ad (I := I) g⁻¹ = (Ad (I := I) g).symm := by
  ext X
  rfl

end TauCeti.Lie
