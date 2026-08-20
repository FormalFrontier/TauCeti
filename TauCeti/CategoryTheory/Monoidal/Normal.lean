/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal
import Mathlib.Tactic.Group

/-!
# Conjugation actions on internal normal subgroups

Let `φ : H ⟶ G` be a normal subgroup object in a cartesian monoidal category. Mathlib's
`CategoryTheory.IsMonHom.Normal` says that conjugation in `G` factors through `φ`. Since `φ` is
monic, that factor is unique. This file names it as `normalConjugation φ` and proves the action
laws directly at the level of generalized points.

Thus conjugation by the identity acts trivially, conjugation by a product is the composite of the
two conjugations, and each conjugation preserves the unit, multiplication, and inverse in `H`.
The pointwise statements avoid choosing an internal-hom object of automorphisms and are exactly
the interface needed to put a semidirect-product group structure on an internal product.

## Main declarations

* `TauCeti.normalConjugation`: the canonical factor of ambient conjugation through a normal
  subgroup object.
* `TauCeti.normalConjugation_comp`: its defining equation after inclusion in the ambient group.
* `TauCeti.normalConjugation_one_left` and `TauCeti.normalConjugation_mul_left`: the group-action
  laws.
* `TauCeti.normalConjugation_one_right`, `TauCeti.normalConjugation_mul_right`, and
  `TauCeti.normalConjugation_inv_right`: conjugation acts by group automorphisms.
* `TauCeti.normalConjugationMulEquiv` and `TauCeti.normalConjugationMulAutHom`: the action by
  automorphisms on generalized points.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15--16.
* J. S. Milne, *Algebraic Groups* (2017), §6.a.

This is the conjugation-action input for Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap. The product of two normal unipotent subgroup schemes is obtained as the
image of multiplication from the semidirect product defined by this action.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u v

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {G H X : C} [GrpObj G] [GrpObj H]

/-- The canonical conjugation action of a group object on a normal subgroup object.

For `φ : H ⟶ G`, the composite `G ⊗ H ⟶ H ⟶ G` is the ambient conjugation morphism
`(g, h) ↦ g * φ(h) * g⁻¹`. Normality supplies a factorization and monicity of `φ` makes it
unique. -/
noncomputable def normalConjugation (φ : H ⟶ G) [IsMonHom.Normal φ] : G ⊗ H ⟶ H :=
  Classical.choose (IsMonHom.Normal.exists_comp_eq_conj φ)

/-- Including the conjugate of a normal-subgroup element gives its ambient conjugate. This is the
defining equation of `normalConjugation`. -/
@[reassoc]
theorem normalConjugation_comp (φ : H ⟶ G) [IsMonHom.Normal φ] :
    normalConjugation φ ≫ φ = G ◁ φ ≫ GrpObj.conj G :=
  Classical.choose_spec (IsMonHom.Normal.exists_comp_eq_conj φ)

/-- The factorization of ambient conjugation through a normal subgroup object is unique. -/
theorem normalConjugation_unique (φ : H ⟶ G) [IsMonHom.Normal φ] (ψ : G ⊗ H ⟶ H)
    (hψ : ψ ≫ φ = G ◁ φ ≫ GrpObj.conj G) :
    ψ = normalConjugation φ := by
  apply (cancel_mono φ).1
  rw [hψ, normalConjugation_comp]

/-- On generalized points, `normalConjugation` is ambient conjugation after applying the subgroup
inclusion. -/
@[reassoc]
theorem lift_normalConjugation_comp (φ : H ⟶ G) [IsMonHom.Normal φ]
    (g : X ⟶ G) (h : X ⟶ H) :
    lift g h ≫ normalConjugation φ ≫ φ = g * (h ≫ φ) * g⁻¹ := by
  rw [normalConjugation_comp]
  simp

/-- Conjugation by the identity fixes every generalized point of a normal subgroup object. -/
@[simp]
theorem normalConjugation_one_left (φ : H ⟶ G) [IsMonHom.Normal φ] (h : X ⟶ H) :
    lift 1 h ≫ normalConjugation φ = h := by
  apply (cancel_mono φ).1
  simp [lift_normalConjugation_comp]

/-- Conjugation fixes the identity generalized point of a normal subgroup object. -/
@[simp]
theorem normalConjugation_one_right (φ : H ⟶ G) [IsMonHom.Normal φ] (g : X ⟶ G) :
    lift g 1 ≫ normalConjugation φ = 1 := by
  apply (cancel_mono φ).1
  simp [lift_normalConjugation_comp]

/-- Conjugation by a product is successive conjugation, with the right factor acting first. -/
theorem normalConjugation_mul_left (φ : H ⟶ G) [IsMonHom.Normal φ]
    (g₁ g₂ : X ⟶ G) (h : X ⟶ H) :
    lift (g₁ * g₂) h ≫ normalConjugation φ =
      lift g₁ (lift g₂ h ≫ normalConjugation φ) ≫ normalConjugation φ := by
  apply (cancel_mono φ).1
  simp [lift_normalConjugation_comp]
  group

/-- Conjugation preserves multiplication in a normal subgroup object. -/
theorem normalConjugation_mul_right (φ : H ⟶ G) [IsMonHom.Normal φ]
    (g : X ⟶ G) (h₁ h₂ : X ⟶ H) :
    lift g (h₁ * h₂) ≫ normalConjugation φ =
      (lift g h₁ ≫ normalConjugation φ) * (lift g h₂ ≫ normalConjugation φ) := by
  apply (cancel_mono φ).1
  simp only [Category.assoc, lift_normalConjugation_comp, MonObj.mul_comp]
  group

/-- Conjugation preserves inverses in a normal subgroup object. -/
@[simp]
theorem normalConjugation_inv_right (φ : H ⟶ G) [IsMonHom.Normal φ]
    (g : X ⟶ G) (h : X ⟶ H) :
    lift g h⁻¹ ≫ normalConjugation φ = (lift g h ≫ normalConjugation φ)⁻¹ := by
  apply (cancel_mono φ).1
  simp only [Category.assoc, lift_normalConjugation_comp, GrpObj.inv_comp]
  group

/-- Conjugation commutes with precomposition of generalized points. -/
theorem comp_normalConjugation (φ : H ⟶ G) [IsMonHom.Normal φ]
    {Y : C} (f : Y ⟶ X) (g : X ⟶ G) (h : X ⟶ H) :
    f ≫ lift g h ≫ normalConjugation φ =
      lift (f ≫ g) (f ≫ h) ≫ normalConjugation φ := by
  rw [← Category.assoc, comp_lift]

/-- Conjugation by an ambient generalized point, as an automorphism of the normal subgroup's
generalized-point group. Its inverse is conjugation by the inverse ambient point. -/
noncomputable def normalConjugationMulEquiv (φ : H ⟶ G) [IsMonHom.Normal φ]
    (g : X ⟶ G) : (X ⟶ H) ≃* (X ⟶ H) where
  toFun h := lift g h ≫ normalConjugation φ
  invFun h := lift g⁻¹ h ≫ normalConjugation φ
  left_inv h := by
    dsimp
    rw [← normalConjugation_mul_left φ g⁻¹ g h, inv_mul_cancel,
      normalConjugation_one_left]
  right_inv h := by
    dsimp
    rw [← normalConjugation_mul_left φ g g⁻¹ h, mul_inv_cancel,
      normalConjugation_one_left]
  map_mul' h₁ h₂ := normalConjugation_mul_right φ g h₁ h₂

/-- Applying the conjugation automorphism is `normalConjugation` on the pair of generalized
points. -/
@[simp]
theorem normalConjugationMulEquiv_apply (φ : H ⟶ G) [IsMonHom.Normal φ]
    (g : X ⟶ G) (h : X ⟶ H) :
    normalConjugationMulEquiv φ g h = lift g h ≫ normalConjugation φ := (rfl)

/-- The inverse conjugation automorphism is conjugation by the inverse ambient point. -/
@[simp]
theorem normalConjugationMulEquiv_symm_apply (φ : H ⟶ G) [IsMonHom.Normal φ]
    (g : X ⟶ G) (h : X ⟶ H) :
    (normalConjugationMulEquiv φ g).symm h = lift g⁻¹ h ≫ normalConjugation φ := (rfl)

/-- The ambient generalized-point group acts on the normal subgroup's generalized points by
conjugation. This is the action homomorphism used by the external semidirect product. -/
noncomputable def normalConjugationMulAutHom (φ : H ⟶ G) [IsMonHom.Normal φ] :
    (X ⟶ G) →* MulAut (X ⟶ H) where
  toFun := normalConjugationMulEquiv φ
  map_one' := by
    ext h
    exact normalConjugation_one_left φ h
  map_mul' g₁ g₂ := by
    ext h
    exact normalConjugation_mul_left φ g₁ g₂ h

/-- The action homomorphism evaluates as the canonical internal conjugation factor. -/
@[simp]
theorem normalConjugationMulAutHom_apply (φ : H ⟶ G) [IsMonHom.Normal φ]
    (g : X ⟶ G) (h : X ⟶ H) :
    normalConjugationMulAutHom φ g h = lift g h ≫ normalConjugation φ := (rfl)

end TauCeti
