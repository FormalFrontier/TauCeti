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
  [LieGroup I ∞ G]

local instance finiteDimensionalCompleteSpaceLieEquiv [FiniteDimensional ℝ E] : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

-- The manifold bracket API needs three derivatives; this instance is the corresponding downgrade of
-- the ambient smooth Lie-group structure.
local instance lieGroupMinSmoothnessThree : LieGroup I (minSmoothness ℝ 3) G :=
  LieGroup.of_le (I := I) (G := G) (m := minSmoothness ℝ 3) (n := ∞)
    (by simpa using (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out)

/-- The map sending a tangent vector at the identity to its left-invariant derivation preserves the
Lie bracket. -/
@[simp]
theorem tangentToLeftInvariantDerivation_lie [CompleteSpace E]
    (v w : GroupLieAlgebra I G) :
    tangentToLeftInvariantDerivation (I := I) (G := G) ⁅v, w⁆ =
      ⁅tangentToLeftInvariantDerivation (I := I) (G := G) v,
        tangentToLeftInvariantDerivation (I := I) (G := G) w⁆ := by
  apply LeftInvariantDerivation.evalAt_one_injective
  ext f
  let F : C^∞⟮I, G; ℝ⟯ := f
  -- Point-derivation extensionality presents `f` as a pointed smooth map, while a global
  -- derivation acts on its canonical global extension `F`.
  have hleft :
      (LeftInvariantDerivation.evalAt (I := I) (1 : G)
        (tangentToLeftInvariantDerivation ⁅v, w⁆)) f =
        (tangentToLeftInvariantDerivation ⁅v, w⁆ F) 1 := rfl
  have hright :
      (LeftInvariantDerivation.evalAt (I := I) (1 : G)
        ⁅tangentToLeftInvariantDerivation v, tangentToLeftInvariantDerivation w⁆) f =
        (⁅tangentToLeftInvariantDerivation v, tangentToLeftInvariantDerivation w⁆ F) 1 := rfl
  rw [hleft, hright]
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
      F.contMDiff.contMDiffAt
      (by simpa using (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out)
      ((contMDiff_mulInvariantVectorField_infty v).mdifferentiable
        (by simp)).mdifferentiableAt
      ((contMDiff_mulInvariantVectorField_infty w).mdifferentiable
        (by simp)).mdifferentiableAt
  exact hbridge.trans (congrArg₂ (· - ·) hwapply.symm hvapply.symm)

/-- Evaluation at the identity identifies left-invariant derivations with the tangent Lie algebra as
Lie algebras. -/
noncomputable def leftInvariantDerivationLieEquivGroupLieAlgebra
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G)) :
    LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ GroupLieAlgebra I G :=
  { leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G) h₁ with
    map_lie' := by
      intro D D'
      let e₀ := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G) h₁
      -- Expose the underlying canonical linear equivalence supplied to this structure literal.
      change e₀ ⁅D, D'⁆ = ⁅e₀ D, e₀ D'⁆
      apply e₀.symm.injective
      rw [e₀.symm_apply_apply]
      rw [leftInvariantDerivationEquivGroupLieAlgebra_symm_apply h₁]
      rw [tangentToLeftInvariantDerivation_lie]
      rw [← leftInvariantDerivationEquivGroupLieAlgebra_symm_apply h₁,
        ← leftInvariantDerivationEquivGroupLieAlgebra_symm_apply h₁]
      rw [e₀.symm_apply_apply, e₀.symm_apply_apply] }

/-- The Lie equivalence acts as the underlying linear equivalence given by evaluation at the
identity. -/
@[simp]
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_apply
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G))
    (D : LeftInvariantDerivation I G) :
    leftInvariantDerivationLieEquivGroupLieAlgebra h₁ D =
      leftInvariantDerivationEquivGroupLieAlgebra h₁ D := by
  rfl

/-- The inverse Lie equivalence sends a tangent vector to its left-invariant derivation. -/
@[simp]
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_symm_apply
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G))
    (v : GroupLieAlgebra I G) :
    (leftInvariantDerivationLieEquivGroupLieAlgebra h₁).symm v =
      tangentToLeftInvariantDerivation v := by
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra h₁
  let e₀ := leftInvariantDerivationEquivGroupLieAlgebra h₁
  apply e.symm_apply_eq.mpr
  rw [leftInvariantDerivationLieEquivGroupLieAlgebra_apply]
  symm
  calc
    e₀ (tangentToLeftInvariantDerivation v) = e₀ (e₀.symm v) := by
      rw [leftInvariantDerivationEquivGroupLieAlgebra_symm_apply]
    _ = v := e₀.apply_symm_apply v

/-- Evaluation at the identity preserves the Lie bracket. -/
@[simp]
theorem leftInvariantDerivationEquivGroupLieAlgebra_lie
    [FiniteDimensional ℝ E] [T2Space G] (h₁ : I.IsInteriorPoint (1 : G))
    (D D' : LeftInvariantDerivation I G) :
    pointDerivationEquivTangentSpace (I := I) 1 h₁
        (LeftInvariantDerivation.evalAt 1 ⁅D, D'⁆) =
      ⁅pointDerivationEquivTangentSpace (I := I) 1 h₁
          (LeftInvariantDerivation.evalAt 1 D),
        pointDerivationEquivTangentSpace (I := I) 1 h₁
          (LeftInvariantDerivation.evalAt 1 D')⁆ := by
  rw [← leftInvariantDerivationEquivGroupLieAlgebra_apply,
    ← leftInvariantDerivationEquivGroupLieAlgebra_apply,
    ← leftInvariantDerivationEquivGroupLieAlgebra_apply]
  simpa only [leftInvariantDerivationLieEquivGroupLieAlgebra_apply] using
    (leftInvariantDerivationLieEquivGroupLieAlgebra h₁).map_lie D D'
