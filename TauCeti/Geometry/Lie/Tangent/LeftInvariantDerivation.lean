/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LeftInvariantDerivation
public import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.DerivationBundle

/-!
# Evaluation of left-invariant derivations

A left-invariant derivation on a Lie group is determined by its value at any point. For a
finite-dimensional smooth real Lie group whose identity is an interior point, evaluation there
gives a canonical linear equivalence between left-invariant derivations and the tangent Lie algebra.

## Main results

* `LeftInvariantDerivation.evalAt_one_injective`: identity evaluation is injective for monoids.
* `LeftInvariantDerivation.evalAt_injective`: evaluation at any point is injective.
* `tangentToLeftInvariantDerivation`: the left-invariant derivation associated to a tangent vector
  at the identity.
* `leftInvariantDerivationEquivGroupLieAlgebra`: the canonical linear equivalence between
  left-invariant derivations and the tangent Lie algebra.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
* The proof of `contMDiff_mulInvariantVectorField_infty` follows Sébastien Gouëzel's proof of
  Mathlib's `contMDiff_mulInvariantVectorField`, specialized to infinite smoothness.
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- A left-invariant vector field on a smooth real Lie group is smooth. -/
theorem contMDiff_mulInvariantVectorField_infty
    [ContMDiffMul I ∞ G] (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞
      (fun g : G ↦ (mulInvariantVectorField v g : TangentBundle I G)) := by
  let fg : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sfg : ContMDiff I I.tangent ∞ fg := contMDiff_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ ↦ TotalSpace.mk' E 1 v
  have sfv : ContMDiff I I.tangent ∞ fv := contMDiff_const
  let F₁ : G → TangentBundle I G × TangentBundle I G := fun g ↦ (fg g, fv g)
  have S₁ : ContMDiff I (I.tangent.prod I.tangent) ∞ F₁ := sfg.prodMk sfv
  let F₂ : TangentBundle I G × TangentBundle I G →
      TangentBundle (I.prod I) (G × G) := (equivTangentBundleProd I G I G).symm
  have S₂ : ContMDiff (I.tangent.prod I.tangent) (I.prod I).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap% (fun p : G × G ↦ p.1 * p.2)
  have S₃ : ContMDiff (I.prod I).tangent I.tangent ∞ F₃ :=
    (contMDiff_mul I ∞).contMDiff_tangentMap (by simp)
  let S := (S₃.comp S₂).comp S₁
  convert! S with g
  · simp [F₁, F₂, F₃, fg, fv]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁, fg, fv]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I ∞).mdifferentiableAt (by simp))]
    simp +instances [mulInvariantVectorField, equivTangentBundleProd]
    rfl

/-- Differentiating a smooth scalar function along a left-invariant vector field gives a smooth
scalar function. -/
theorem contMDiff_mvfderiv_mulInvariantVectorField
    [ContMDiffMul I ∞ G] (v : GroupLieAlgebra I G)
    (f : C^∞⟮I, G; ℝ⟯) :
    ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      (fun g ↦ mvfderiv I f g (mulInvariantVectorField v g)) := by
  let df : TangentBundle I G → TangentBundle (modelWithCornersSelf ℝ ℝ) ℝ :=
    tangentMap% (f : G → ℝ)
  have hdf : ContMDiff I.tangent (modelWithCornersSelf ℝ ℝ).tangent ∞ df :=
    f.contMDiff.contMDiff_tangentMap (by simp)
  have hsnd : ContMDiff (modelWithCornersSelf ℝ ℝ).tangent
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : TangentBundle (modelWithCornersSelf ℝ ℝ) ℝ ↦ p.2) :=
    contMDiff_snd_tangentBundle_modelSpace ℝ (modelWithCornersSelf ℝ ℝ)
  -- `mvfderiv` is the second component of the tangent map, hidden by bundle coercions.
  change ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
    (fun g ↦ mfderiv I (modelWithCornersSelf ℝ ℝ) f g (mulInvariantVectorField v g))
  have h := hsnd.comp (hdf.comp (contMDiff_mulInvariantVectorField_infty v))
  exact h.congr fun g ↦ rfl

/-- At the identity, the invariant vector field generated by `v` equals `v`. -/
@[simp]
theorem mulInvariantVectorField_one (v : GroupLieAlgebra I G) :
    mulInvariantVectorField v (1 : G) = v := by
  -- Unfold the invariant field to expose the derivative of the identity map.
  change mfderiv I I (fun x : G ↦ 1 * x) 1 v = v
  rw [show (fun x : G ↦ 1 * x) = id by funext x; simp, mfderiv_id]
  rfl

/-- The left-invariant derivation associated to a tangent vector at the identity. At every point it
acts by differentiating along Mathlib's corresponding left-invariant vector field. -/
noncomputable def tangentToLeftInvariantDerivation
    [ContMDiffMul I ∞ G] :
    GroupLieAlgebra I G →ₗ[ℝ] LeftInvariantDerivation I G where
  toFun v := by
    let D : Derivation ℝ C^∞⟮I, G; ℝ⟯ C^∞⟮I, G; ℝ⟯ :=
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
    refine { toDerivation := D, left_invariant'' := fun g ↦ ?_ }
    · ext f
      -- The calculation endpoints unfold `hfdifferential`, `evalAt`, and the local derivation `D`.
      calc
        ((𝒅ₕ (smoothLeftMul_one I g))
            (Derivation.evalAt 1 D)) f =
            mvfderiv I ((show C^∞⟮I, G; ℝ⟯ from f).comp (smoothLeftMul I g)) 1
              (mulInvariantVectorField v 1) := rfl
        _ = mvfderiv I ((show C^∞⟮I, G; ℝ⟯ from f).comp (smoothLeftMul I g)) 1 v := by
          rw [mulInvariantVectorField_one]
        _ = mvfderiv I (show C^∞⟮I, G; ℝ⟯ from f) g
            (mulInvariantVectorField v g) := by
          rw [mulInvariantVectorField]
          -- Expose the function composition hidden by `ContMDiffMap.comp`.
          change (mfderiv I (modelWithCornersSelf ℝ ℝ) (fun x ↦ f (g * x)) 1) v =
            (mfderiv I (modelWithCornersSelf ℝ ℝ) f g)
              ((mfderiv I I (fun x ↦ g * x) 1) v)
          have h := mfderiv_comp_apply 1
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
            ((contMDiff_mul_left (n := ∞) (a := g)).mdifferentiable (by simp)).mdifferentiableAt v
          rw [mul_one] at h
          change ((mfderiv I (modelWithCornersSelf ℝ ℝ)
            ((show G → ℝ from f) ∘ fun x ↦ g * x) 1) v) = _
          exact h
        _ = (Derivation.evalAt g D) f := rfl
  map_add' v w := by
    apply LeftInvariantDerivation.evalAt_one_injective
    ext f
    -- Evaluation unfolds both constructed derivations to directional derivatives.
    change mvfderiv I f 1 (mulInvariantVectorField (v + w) 1) =
      mvfderiv I f 1 (mulInvariantVectorField v 1) +
        mvfderiv I f 1 (mulInvariantVectorField w 1)
    simp
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
    (f : C^∞⟮I, G; ℝ⟯) (g : G) :
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
