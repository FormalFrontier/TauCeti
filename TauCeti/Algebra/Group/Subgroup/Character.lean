/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation of characters of a normal subgroup

If `N` is a normal subgroup of `G`, inverse conjugation by an ambient element acts on
monoid-valued characters of `N`. This file packages that action as an equivalence of the
character set.

## Main declarations

* `MonoidHom.conjNormal`: precomposition of a character with inverse conjugation.
* `MonoidHom.conjNormalEquiv`: conjugation by an ambient element as an equivalence of the
  character set of a normal subgroup.
-/

public section

namespace TauCeti

variable {G A : Type*} [Group G] [Monoid A]

/-- Inverse conjugation is the inverse of conjugation on a normal subgroup. -/
theorem _root_.MulAut.conjNormal_inv {N : Subgroup G} [N.Normal] (g : G) :
    (MulAut.conjNormal (H := N)) g⁻¹ = ((MulAut.conjNormal (H := N)) g).symm := by
  exact (map_inv (MulAut.conjNormal (H := N)) g).trans
    (MulAut.inv_def N ((MulAut.conjNormal (H := N)) g))

/-- Precomposition by inverse conjugation gives the action of an ambient group element on
characters of a normal subgroup. Thus `(conjNormal g χ) n = χ (g⁻¹ * n * g)`. -/
def _root_.MonoidHom.conjNormal {N : Subgroup G} [N.Normal]
    (g : G) (χ : N →* A) : N →* A :=
  χ.comp (MulAut.conjNormal g⁻¹).toMonoidHom

@[simp]
theorem _root_.MonoidHom.conjNormal_apply {N : Subgroup G} [N.Normal] (g : G)
    (χ : N →* A) (n : N) :
    MonoidHom.conjNormal g χ n = χ ((MulAut.conjNormal g).symm n) := by
  rfl

@[simp]
theorem _root_.MonoidHom.conjNormal_one {N : Subgroup G} [N.Normal] (χ : N →* A) :
    MonoidHom.conjNormal 1 χ = χ := by
  ext n
  simp [MonoidHom.conjNormal]

/-- Conjugating characters is a left action: `g₁ * g₂` first acts by `g₂`, then by `g₁`. -/
theorem _root_.MonoidHom.conjNormal_mul {N : Subgroup G} [N.Normal]
    (g₁ g₂ : G) (χ : N →* A) :
    MonoidHom.conjNormal (g₁ * g₂) χ =
      MonoidHom.conjNormal g₁ (MonoidHom.conjNormal g₂ χ) := by
  ext n
  simp only [MonoidHom.conjNormal_apply]
  apply congrArg χ
  apply Subtype.ext
  simp only [MulAut.conjNormal_symm_apply]
  simp [mul_assoc]

@[simp]
theorem _root_.MonoidHom.conjNormal_inv_apply_conjNormal {N : Subgroup G} [N.Normal]
    (g : G) (χ : N →* A) :
    MonoidHom.conjNormal g⁻¹ (MonoidHom.conjNormal g χ) = χ := by
  simp only [← MonoidHom.conjNormal_mul, inv_mul_cancel, MonoidHom.conjNormal_one]

@[simp]
theorem _root_.MonoidHom.conjNormal_apply_inv_conjNormal {N : Subgroup G} [N.Normal]
    (g : G) (χ : N →* A) :
    MonoidHom.conjNormal g (MonoidHom.conjNormal g⁻¹ χ) = χ := by
  simp only [← MonoidHom.conjNormal_mul, mul_inv_cancel, MonoidHom.conjNormal_one]

/-- Conjugation by `g` is an equivalence of the character set of a normal subgroup, with
inverse given by conjugation by `g⁻¹`. -/
def _root_.MonoidHom.conjNormalEquiv (N : Subgroup G) [N.Normal]
    (A : Type*) [Monoid A] (g : G) :
    (N →* A) ≃ (N →* A) where
  toFun := MonoidHom.conjNormal g
  invFun := MonoidHom.conjNormal g⁻¹
  left_inv := MonoidHom.conjNormal_inv_apply_conjNormal g
  right_inv := MonoidHom.conjNormal_apply_inv_conjNormal g

@[simp]
theorem _root_.MonoidHom.conjNormalEquiv_apply {N : Subgroup G} [N.Normal]
    (g : G) (χ : N →* A) :
    MonoidHom.conjNormalEquiv N A g χ = MonoidHom.conjNormal g χ :=
  by simp [MonoidHom.conjNormalEquiv]

@[simp]
theorem _root_.MonoidHom.conjNormalEquiv_symm {N : Subgroup G} [N.Normal] (g : G) :
    (MonoidHom.conjNormalEquiv N A g).symm = MonoidHom.conjNormalEquiv N A g⁻¹ := by
  ext χ n
  simp [MonoidHom.conjNormalEquiv]

end TauCeti
