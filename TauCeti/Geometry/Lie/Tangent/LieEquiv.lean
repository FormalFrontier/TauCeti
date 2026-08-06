/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Lie.Tangent.LeftInvariantDerivation

/-!
# The Lie equivalence between derivations and the identity tangent space

For a finite-dimensional smooth real Lie group whose identity is an interior point, the canonical
linear equivalence between left-invariant derivations and the tangent space at the identity is an
equivalence of Lie algebras. This supplies the bracket-compatible dictionary needed to transport the
tangent adjoint action to Mathlib's roadmap-facing Lie algebra `LeftInvariantDerivation I G`.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main results

* `tangentToLeftInvariantDerivation_lie`: the invariant derivation construction preserves brackets.
* `leftInvariantDerivationLieEquivGroupLieAlgebra`: the canonical derivation–tangent Lie
  equivalence.

## References

* `Mathlib/Geometry/Manifold/GroupLieAlgebra.lean`, whose compatibility TODO this file discharges.
* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

noncomputable section

open Manifold VectorField
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [CompleteSpace E] [LieGroup I ∞ G]

-- The manifold bracket API needs three derivatives; this instance is the corresponding downgrade of
-- the ambient smooth Lie-group structure.
local instance lieGroupMinSmoothnessThree : LieGroup I (minSmoothness ℝ 3) G :=
  LieGroup.of_le (I := I) (G := G) (m := minSmoothness ℝ 3) (n := ∞)
    (by simpa using (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out)

/-- The map sending a tangent vector at the identity to its left-invariant derivation preserves the
Lie bracket. -/
@[simp]
theorem tangentToLeftInvariantDerivation_lie (v w : GroupLieAlgebra I G) :
    tangentToLeftInvariantDerivation (I := I) (G := G) ⁅v, w⁆ =
      ⁅tangentToLeftInvariantDerivation (I := I) (G := G) v,
        tangentToLeftInvariantDerivation (I := I) (G := G) w⁆ := by
  apply LeftInvariantDerivation.evalAt_one_injective
  ext f
  let F : C^∞⟮I, G; ℝ⟯ := f
  change (tangentToLeftInvariantDerivation (I := I) (G := G) ⁅v, w⁆ F) 1 =
    (⁅tangentToLeftInvariantDerivation (I := I) (G := G) v,
      tangentToLeftInvariantDerivation (I := I) (G := G) w⁆ F) 1
  rw [LeftInvariantDerivation.commutator_apply]
  simp only [tangentToLeftInvariantDerivation_apply, ContMDiffMap.coe_sub, Pi.sub_apply]
  rw [mulInvariantVectorField_one, GroupLieAlgebra.bracket_def]
  have hvfun : (⇑((tangentToLeftInvariantDerivation v) F) : G → ℝ) =
      fun y ↦ mvfderiv I F y (mulInvariantVectorField v y) := by
    funext y
    exact tangentToLeftInvariantDerivation_apply v F y
  have hwfun : (⇑((tangentToLeftInvariantDerivation w) F) : G → ℝ) =
      fun y ↦ mvfderiv I F y (mulInvariantVectorField w y) := by
    funext y
    exact tangentToLeftInvariantDerivation_apply w F y
  have hvapply := congrArg
    (fun L : E →L[ℝ] ℝ ↦ L (mulInvariantVectorField w (1 : G)))
    (mfderiv_congr (I := I) (I' := 𝓘(ℝ, ℝ)) (x := (1 : G)) hvfun)
  have hwapply := congrArg
    (fun L : E →L[ℝ] ℝ ↦ L (mulInvariantVectorField v (1 : G)))
    (mfderiv_congr (I := I) (I' := 𝓘(ℝ, ℝ)) (x := (1 : G)) hwfun)
  have hbridge :=
    mvfderiv_mlieBracket
      (f := (F : G → ℝ))
      (V := mulInvariantVectorField v)
      (W := mulInvariantVectorField w)
      (x := (1 : G))
      (by norm_num)
      (F.contMDiff.contMDiffAt.of_le (show
        ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) from
          WithTop.coe_le_coe.mpr le_top))
      ((contMDiff_mulInvariantVectorField_infty v).mdifferentiable
        (by simp)).mdifferentiableAt
      ((contMDiff_mulInvariantVectorField_infty w).mdifferentiable
        (by simp)).mdifferentiableAt
      ((contMDiff_mvfderiv_mulInvariantVectorField v F).mdifferentiable
        (by simp)).mdifferentiableAt
      ((contMDiff_mvfderiv_mulInvariantVectorField w F).mdifferentiable
        (by simp)).mdifferentiableAt
  exact hbridge.trans (congrArg₂ (· - ·) hwapply.symm hvapply.symm)

private noncomputable def tangentToLeftInvariantDerivationLieHom
    : GroupLieAlgebra I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I G :=
  { toLinearMap := tangentToLeftInvariantDerivation (I := I) (G := G)
    map_lie' := by
      intro v w
      exact tangentToLeftInvariantDerivation_lie (I := I) (G := G) v w }

/-- The tangent Lie algebra at the identity is canonically Lie-equivalent to the algebra of
left-invariant derivations. -/
private noncomputable def groupLieAlgebraLieEquivLeftInvariantDerivation
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G)) :
    GroupLieAlgebra I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G :=
  LieEquiv.ofBijective (tangentToLeftInvariantDerivationLieHom (I := I) (G := G))
    (by
      let e := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G) h₁
      have hfun :
          (tangentToLeftInvariantDerivationLieHom (I := I) (G := G) :
            GroupLieAlgebra I G → LeftInvariantDerivation I G) = e.symm := by
        funext v
        exact leftInvariantDerivationEquivGroupLieAlgebra_symm_apply h₁ v |>.symm
      rw [hfun]
      exact e.symm.bijective)

/-- Evaluation at the identity identifies left-invariant derivations with the tangent Lie algebra as
Lie algebras. -/
noncomputable def leftInvariantDerivationLieEquivGroupLieAlgebra
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G)) :
    LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ GroupLieAlgebra I G :=
  (groupLieAlgebraLieEquivLeftInvariantDerivation (I := I) (G := G) h₁).symm

/-- The inverse Lie equivalence sends a tangent vector to its left-invariant derivation. -/
@[simp]
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_symm_apply
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G))
    (v : GroupLieAlgebra I G) :
    (leftInvariantDerivationLieEquivGroupLieAlgebra h₁).symm v =
      tangentToLeftInvariantDerivation v := by
  simp [leftInvariantDerivationLieEquivGroupLieAlgebra,
    groupLieAlgebraLieEquivLeftInvariantDerivation,
    tangentToLeftInvariantDerivationLieHom]
  rfl

/-- The Lie equivalence acts as the underlying linear equivalence given by evaluation at the
identity. -/
@[simp]
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_apply
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G))
    (D : LeftInvariantDerivation I G) :
    leftInvariantDerivationLieEquivGroupLieAlgebra h₁ D =
      leftInvariantDerivationEquivGroupLieAlgebra h₁ D := by
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra h₁
  let e₀ := leftInvariantDerivationEquivGroupLieAlgebra h₁
  have hright : e.symm (e₀ D) = D := by
    calc
      e.symm (e₀ D) = tangentToLeftInvariantDerivation (e₀ D) :=
        leftInvariantDerivationLieEquivGroupLieAlgebra_symm_apply h₁ (e₀ D)
      _ = e₀.symm (e₀ D) :=
        (leftInvariantDerivationEquivGroupLieAlgebra_symm_apply h₁ (e₀ D)).symm
      _ = D := e₀.symm_apply_apply D
  exact e.symm.injective ((e.symm_apply_apply D).trans hright.symm)
