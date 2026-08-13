/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LeftInvariantDerivation
public import TauCeti.Geometry.Manifold.DerivationBundle
public import TauCeti.Geometry.Lie.InvariantVectorField.Basic

/-!
# Evaluation of left-invariant derivations

A left-invariant derivation on a Lie group is determined by its value at any point. For a
finite-dimensional smooth real Lie group whose identity is an interior point, evaluation there
gives a canonical linear equivalence between left-invariant derivations and the tangent Lie algebra.
The latter is the manifold model vector space, so this also determines the Lie algebra's dimension.

## Main results

* `LeftInvariantDerivation.evalAt_one_injective`: identity evaluation is injective for monoids.
* `LeftInvariantDerivation.evalAt_injective`: evaluation at any point is injective.
* `tangentToLeftInvariantDerivation`: the left-invariant derivation associated to a tangent vector
  at the identity.
* `leftInvariantDerivationEquivGroupLieAlgebra`: the canonical linear equivalence between
  left-invariant derivations and the tangent Lie algebra.
* `leftInvariantDerivationLinearIsometryEquivModelVectorSpace`: the canonical isometric linear
  equivalence with the manifold model vector space.
* `finiteDimensional_leftInvariantDerivation`: the Lie algebra is finite-dimensional.
* `finrank_leftInvariantDerivation_eq_modelVectorSpace`: its dimension equals that of the manifold
  model vector space.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
-/

public section

open scoped ContDiff Manifold

namespace LeftInvariantDerivation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]

/-- A left-invariant derivation on a monoid is determined by its value at the identity. -/
theorem evalAt_one_injective [Monoid G] [ContMDiffMul I ∞ G] :
    Function.Injective (evalAt (I := I) (1 : G)) := by
  intro X Y hXY
  ext f g
  have hEval : evalAt (I := I) g X = evalAt (I := I) g Y := by
    calc
      evalAt (I := I) g X =
          𝒅ₕ (smoothLeftMul_one I g) (evalAt (I := I) (1 : G) X) :=
        (left_invariant (I := I) (g := g) (X := X)).symm
      _ = 𝒅ₕ (smoothLeftMul_one I g) (evalAt (I := I) (1 : G) Y) :=
        congrArg (𝒅ₕ (smoothLeftMul_one I g)) hXY
      _ = evalAt (I := I) g Y := left_invariant (I := I) (g := g) (X := Y)
  rw [← evalAt_apply (I := I) (g := g) (X := X) (f := f),
    ← evalAt_apply (I := I) (g := g) (X := Y) (f := f)]
  exact congrArg (fun D => D f) hEval

/-- A left-invariant derivation is determined by its value at any point. -/
theorem evalAt_injective [Group G] [ContMDiffMul I ∞ G] (g₀ : G) :
    Function.Injective (evalAt (I := I) g₀) := by
  intro X Y hXY
  have hOne : evalAt (I := I) (1 : G) X = evalAt (I := I) (1 : G) Y := by
    have hInv : evalAt (I := I) (g₀⁻¹ * g₀) X = evalAt (I := I) (g₀⁻¹ * g₀) Y := by
      rw [evalAt_mul, evalAt_mul, hXY]
    rw [inv_mul_cancel] at hInv
    exact hInv
  exact evalAt_one_injective hOne

end LeftInvariantDerivation

open Bundle Function Manifold VectorField
open scoped LieGroup

section Construction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- Differentiating a smooth scalar function along a left-invariant vector field gives a smooth
scalar function. -/
theorem contMDiff_mvfderiv_mulInvariantVectorField
    [ContMDiffMul I ∞ G] (v : GroupLieAlgebra I G)
    (f : C^∞⟮I, G; 𝕜⟯) :
    ContMDiff I (modelWithCornersSelf 𝕜 𝕜) ∞
      (fun g ↦ mvfderiv I f g (mulInvariantVectorField v g)) :=
  (f.contMDiff.contMDiff_mvfderiv_apply (by simp)).comp
    (contMDiff_mulInvariantVectorField_infty v)

/-- The derivation of smooth functions that differentiates along the left-invariant vector
field of a tangent vector `v` at the identity. -/
private noncomputable def mulInvariantDerivation [ContMDiffMul I ∞ G]
    (v : GroupLieAlgebra I G) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ :=
  Derivation.mk'
      { toFun := fun f ↦
          ⟨fun g ↦ mvfderiv I f g (mulInvariantVectorField v g),
            contMDiff_mvfderiv_mulInvariantVectorField v f⟩
        map_add' := fun f g ↦ by
          ext x
          -- Unfold the smooth-function wrappers to use linearity of `mvfderiv`.
          change mvfderiv I (⇑f + ⇑g) x (mulInvariantVectorField v x) =
            mvfderiv I f x (mulInvariantVectorField v x) +
              mvfderiv I g x (mulInvariantVectorField v x)
          exact congr($(mvfderiv_add
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
            (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt)
            (mulInvariantVectorField v x))
        map_smul' := fun c f ↦ by
          ext x
          have hc : MDiffAt (fun _ : G ↦ c) x := mdifferentiableAt_const
          -- Unfold the smooth-function wrappers to use the product rule for `mvfderiv`.
          change mvfderiv I ((fun _ : G ↦ c) • ⇑f) x (mulInvariantVectorField v x) =
            c • mvfderiv I f x (mulInvariantVectorField v x)
          have h := congr($(mvfderiv_smul hc
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt)
            (mulInvariantVectorField v x))
          calc
            _ = (c • mvfderiv I f x +
                (mvfderiv I (fun _ : G ↦ c) x).smulRight (f x))
                (mulInvariantVectorField v x) := h
            _ = _ := by simp [mvfderiv_const] }
      fun f g ↦ by
        ext x
        -- Unfold the smooth-function wrappers to use the product rule for `mvfderiv`.
        change mvfderiv I (⇑f * ⇑g) x (mulInvariantVectorField v x) =
          f x * mvfderiv I g x (mulInvariantVectorField v x) +
            g x * mvfderiv I f x (mulInvariantVectorField v x)
        exact congr($(mvfderiv_mul
          (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
          (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt)
          (mulInvariantVectorField v x))

/-- `mulInvariantDerivation v` is left invariant: differentiating along a left-invariant
vector field commutes with left translation. -/
private theorem mulInvariantDerivation_left_invariant [ContMDiffMul I ∞ G]
    (v : GroupLieAlgebra I G) (g : G) :
    (𝒅ₕ (smoothLeftMul_one I g)) (Derivation.evalAt 1 (mulInvariantDerivation v)) =
      Derivation.evalAt g (mulInvariantDerivation v) := by
  ext f
  -- The calculation endpoints unfold `hfdifferential`, `evalAt` and `mulInvariantDerivation`.
  calc
    ((𝒅ₕ (smoothLeftMul_one I g))
        (Derivation.evalAt 1 (mulInvariantDerivation v))) f =
        mvfderiv I ((show C^∞⟮I, G; 𝕜⟯ from f).comp (smoothLeftMul I g)) 1
          (mulInvariantVectorField v 1) := rfl
    _ = mvfderiv I ((show C^∞⟮I, G; 𝕜⟯ from f).comp (smoothLeftMul I g)) 1 v := by
      rw [mulInvariantVectorField_one]
    _ = mvfderiv I (show C^∞⟮I, G; 𝕜⟯ from f) g
        (mulInvariantVectorField v g) := by
      rw [mulInvariantVectorField]
      -- Expose the function composition hidden by `ContMDiffMap.comp`.
      change (mfderiv I (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ f (g * x)) 1) v =
        (mfderiv I (modelWithCornersSelf 𝕜 𝕜) f g)
          ((mfderiv I I (fun x ↦ g * x) 1) v)
      have h := mfderiv_comp_apply 1
        (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
        ((contMDiff_mul_left (n := ∞) (a := g)).mdifferentiable (by simp)).mdifferentiableAt v
      rw [mul_one] at h
      change ((mfderiv I (modelWithCornersSelf 𝕜 𝕜)
        ((show G → 𝕜 from f) ∘ fun x ↦ g * x) 1) v) = _
      exact h
    _ = (Derivation.evalAt g (mulInvariantDerivation v)) f := rfl

/-- The left-invariant derivation associated to a tangent vector at the identity. At every point it
acts by differentiating along Mathlib's corresponding left-invariant vector field. -/
noncomputable def tangentToLeftInvariantDerivation
    [ContMDiffMul I ∞ G] :
    GroupLieAlgebra I G →ₗ[𝕜] LeftInvariantDerivation I G where
  toFun v :=
    { toDerivation := mulInvariantDerivation v
      left_invariant'' := mulInvariantDerivation_left_invariant v }
  map_add' v w := by
    apply LeftInvariantDerivation.evalAt_one_injective
    ext f
    -- Evaluation unfolds both constructed derivations to directional derivatives.
    change mvfderiv I f 1 (mulInvariantVectorField (v + w) 1) =
      mvfderiv I f 1 (mulInvariantVectorField v 1) +
        mvfderiv I f 1 (mulInvariantVectorField w 1)
    simp only [mulInvariantVectorField_add, Pi.add_apply, map_add]
  map_smul' c v := by
    apply LeftInvariantDerivation.evalAt_one_injective
    ext f
    -- Evaluation unfolds both constructed derivations to directional derivatives.
    change mvfderiv I f 1 (mulInvariantVectorField (c • v) 1) =
      c • mvfderiv I f 1 (mulInvariantVectorField v 1)
    simp

/-- The derivation built from a tangent vector acts pointwise along its invariant vector field. -/
@[simp]
theorem tangentToLeftInvariantDerivation_apply
    [ContMDiffMul I ∞ G] (v : GroupLieAlgebra I G)
    (f : C^∞⟮I, G; 𝕜⟯) (g : G) :
    tangentToLeftInvariantDerivation v f g =
      mvfderiv I f g (mulInvariantVectorField v g) :=
  by rfl

/-- Evaluating the derivation associated to `v` at the identity gives directional differentiation
along `v`. -/
@[simp]
theorem LeftInvariantDerivation.evalAt_one_tangentToLeftInvariantDerivation
    [ContMDiffMul I ∞ G] (v : GroupLieAlgebra I G) :
    LeftInvariantDerivation.evalAt (I := I) (1 : G) (tangentToLeftInvariantDerivation v) =
      tangentToPointDerivation (1 : G) v := by
  ext f
  -- Unfold evaluation and the two directional-derivative constructors.
  change mvfderiv I f 1 (mulInvariantVectorField v 1) = mvfderiv I f 1 v
  rw [mulInvariantVectorField_one]

end Construction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- Evaluation at the identity is onto point derivations on a finite-dimensional smooth real Lie
group. -/
theorem LeftInvariantDerivation.evalAt_one_surjective
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    (h₁ : I.IsInteriorPoint (1 : G)) :
    Function.Surjective (LeftInvariantDerivation.evalAt (I := I) (1 : G)) := by
  intro D
  refine ⟨tangentToLeftInvariantDerivation (I := I) (G := G)
    (pointDerivationEquivTangentSpace (I := I) 1 h₁ D), ?_⟩
  rw [evalAt_one_tangentToLeftInvariantDerivation,
    tangentToPointDerivation_pointDerivationEquivTangentSpace]

/-- Left-invariant derivations are canonically linearly equivalent to the tangent Lie algebra at
the identity. -/
noncomputable def leftInvariantDerivationEquivGroupLieAlgebra
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    (h₁ : I.IsInteriorPoint (1 : G)) :
    LeftInvariantDerivation I G ≃ₗ[ℝ] GroupLieAlgebra I G :=
  (LinearEquiv.ofBijective (LeftInvariantDerivation.evalAt (I := I) (1 : G))
    ⟨LeftInvariantDerivation.evalAt_one_injective,
      LeftInvariantDerivation.evalAt_one_surjective h₁⟩).trans
    (pointDerivationEquivTangentSpace 1 h₁)

noncomputable instance LeftInvariantDerivation.instNormedAddCommGroup
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    [BoundarylessManifold I G] : NormedAddCommGroup (LeftInvariantDerivation I G) :=
  NormedAddCommGroup.induced (LeftInvariantDerivation I G) E
    ((leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint).trans
      (LinearEquiv.refl ℝ E))
    ((leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint).trans
      (LinearEquiv.refl ℝ E)).injective

noncomputable instance LeftInvariantDerivation.instNormedSpace
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    [BoundarylessManifold I G] : NormedSpace ℝ (LeftInvariantDerivation I G) :=
  NormedSpace.induced ℝ (LeftInvariantDerivation I G) E
    ((leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint).trans
      (LinearEquiv.refl ℝ E))

/-- The derivation–tangent equivalence is evaluation at the identity followed by the
point-derivation–tangent equivalence. -/
@[simp]
theorem leftInvariantDerivationEquivGroupLieAlgebra_apply
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    (h₁ : I.IsInteriorPoint (1 : G)) (D : LeftInvariantDerivation I G) :
    leftInvariantDerivationEquivGroupLieAlgebra h₁ D =
      pointDerivationEquivTangentSpace 1 h₁ (LeftInvariantDerivation.evalAt 1 D) :=
  by rfl

/-- The inverse derivation–tangent equivalence is the explicit invariant-derivation construction. -/
@[simp]
theorem leftInvariantDerivationEquivGroupLieAlgebra_symm_apply
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    (h₁ : I.IsInteriorPoint (1 : G)) (v : GroupLieAlgebra I G) :
    (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G) h₁).symm v =
      tangentToLeftInvariantDerivation v := by
  apply (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G) h₁).injective
  rw [LinearEquiv.apply_symm_apply, leftInvariantDerivationEquivGroupLieAlgebra_apply]
  rw [LeftInvariantDerivation.evalAt_one_tangentToLeftInvariantDerivation,
    pointDerivationEquivTangentSpace_tangentToPointDerivation]

/-- Evaluation at the identity identifies left-invariant derivations isometrically with the
manifold model vector space. -/
noncomputable def leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    [BoundarylessManifold I G] : LeftInvariantDerivation I G ≃ₗᵢ[ℝ] E where
  toLinearEquiv :=
    (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint).trans
      (LinearEquiv.refl ℝ E)
  norm_map' _ := rfl

/-- The isometric derivation–model-space equivalence is evaluation at the identity followed by
the canonical identification of the identity tangent space with the model vector space. -/
@[simp]
theorem leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    [BoundarylessManifold I G] (X : LeftInvariantDerivation I G) :
    leftInvariantDerivationLinearIsometryEquivModelVectorSpace (I := I) (G := G) X =
      (leftInvariantDerivationEquivGroupLieAlgebra BoundarylessManifold.isInteriorPoint X : E) :=
  (rfl)

/-- The inverse isometric model-space equivalence constructs the canonical left-invariant
derivation generated by the corresponding tangent vector. -/
@[simp]
theorem leftInvariantDerivationLinearIsometryEquivModelVectorSpace_symm_apply
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    [BoundarylessManifold I G] (v : E) :
    (leftInvariantDerivationLinearIsometryEquivModelVectorSpace
      (I := I) (G := G)).symm v =
      tangentToLeftInvariantDerivation (v : GroupLieAlgebra I G) := by
  calc
    _ = (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint).symm (v : GroupLieAlgebra I G) := (rfl)
    _ = _ := leftInvariantDerivationEquivGroupLieAlgebra_symm_apply
      BoundarylessManifold.isInteriorPoint (v : GroupLieAlgebra I G)

/-- The norm of a left-invariant derivation is the norm of its tangent vector at the identity. -/
@[simp]
theorem norm_leftInvariantDerivation_eq_norm_modelVectorSpace
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    [BoundarylessManifold I G] (X : LeftInvariantDerivation I G) :
    ‖X‖ = ‖leftInvariantDerivationLinearIsometryEquivModelVectorSpace
      (I := I) (G := G) X‖ :=
  (leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)).norm_map X |>.symm

/-- The canonical linear identification of the identity tangent space with the model vector
space. -/
noncomputable abbrev groupLieAlgebraEquivModelVectorSpace :
    GroupLieAlgebra I G ≃ₗ[ℝ] E :=
  LinearEquiv.refl ℝ E

/-- Left-invariant derivations on a finite-dimensional smooth real Lie group form a
finite-dimensional vector space. -/
theorem finiteDimensional_leftInvariantDerivation
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    (h₁ : I.IsInteriorPoint (1 : G)) : FiniteDimensional ℝ (LeftInvariantDerivation I G) := by
  let _ : FiniteDimensional ℝ (GroupLieAlgebra I G) :=
    (groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)).symm.finiteDimensional
  exact (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    h₁).symm.finiteDimensional

/-- The Lie algebra of a finite-dimensional smooth real Lie group has the dimension of the
manifold model vector space. -/
theorem finrank_leftInvariantDerivation_eq_modelVectorSpace
    [FiniteDimensional ℝ E] [ContMDiffMul I ∞ G] [T2Space G]
    (h₁ : I.IsInteriorPoint (1 : G)) :
    Module.finrank ℝ (LeftInvariantDerivation I G) = Module.finrank ℝ E := by
  exact LinearEquiv.finrank_eq
    ((leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G) h₁).trans
      (groupLieAlgebraEquivModelVectorSpace (I := I) (G := G)))
