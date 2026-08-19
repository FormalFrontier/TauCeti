/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Binary biproduct squares

This file records generic categorical properties of binary biproducts. A biproduct map factors
through the maps obtained by changing one summand at a time, the squares obtained by adjoining
an identity summand are pushouts or pullbacks, and a zero summand may be deleted.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A binary biproduct map factors by changing its first and second summands in succession. -/
theorem biprod_map_factor {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ X₂]
    [HasBinaryBiproduct Y₁ Y₂] :
    biprod.map f g = biprod.map f (𝟙 X₂) ≫ biprod.map (𝟙 Y₁) g := by
  ext <;> simp

/-- The square formed by a morphism and the corresponding biproduct inclusions is a pushout. -/
theorem isPushout_biprod_inl_map {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryBiproduct X Z] [HasBinaryBiproduct Y Z] :
    IsPushout (biprod.inl : X ⟶ X ⊞ Z) f (biprod.map f (𝟙 Z))
      (biprod.inl : Y ⟶ Y ⊞ Z) :=
  (IsPushout.of_coprod_inl_with_id f Z).of_iso
    (Iso.refl X) (biprod.isoCoprod X Z).symm
    (Iso.refl Y) (biprod.isoCoprod Y Z).symm
    (by simp [coprod.inl_desc]) (by simp) (by ext <;> simp) (by simp [coprod.inl_desc])

/-- The square formed by a morphism and the corresponding biproduct projections is a pullback. -/
theorem isPullback_biprod_map_fst {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryBiproduct X Z] [HasBinaryBiproduct Y Z] :
    IsPullback (biprod.fst : X ⊞ Z ⟶ X) (biprod.map f (𝟙 Z)) f
      (biprod.fst : Y ⊞ Z ⟶ Y) :=
  (IsPullback.of_prod_fst_with_id f Z).of_iso
    (biprod.isoProd X Z).symm (Iso.refl X)
    (biprod.isoProd Y Z).symm (Iso.refl Y)
    (by simp) (by ext <;> simp) (by simp) (by simp)

section Unitors

variable [HasZeroObject C]

open ZeroObject

/-- The right unitor of the binary biproduct: a zero second summand may be deleted. -/
noncomputable def biprodRightUnitor (X : C) [HasBinaryBiproduct X (0 : C)] : X ⊞ (0 : C) ≅ X where
  hom := biprod.fst
  inv := biprod.inl
  hom_inv_id := by
    refine biprod.hom_ext _ _ (by simp) ?_
    simpa using ((isZero_zero C).eq_of_tgt 0 biprod.snd)
  inv_hom_id := by simp

-- These projection lemmas deliberately have non-`rfl` proofs so the unitor bodies remain hidden.
/-- The forward map of the right biproduct unitor is the first projection. -/
@[simp]
lemma biprodRightUnitor_hom (X : C) [HasBinaryBiproduct X (0 : C)] :
    (biprodRightUnitor X).hom = biprod.fst := by
  change (biprod.fst : X ⊞ (0 : C) ⟶ X) = biprod.fst
  exact (Category.comp_id _).symm.trans (Category.comp_id _)

/-- The inverse map of the right biproduct unitor is the first inclusion. -/
@[simp]
lemma biprodRightUnitor_inv (X : C) [HasBinaryBiproduct X (0 : C)] :
    (biprodRightUnitor X).inv = biprod.inl := by
  change (biprod.inl : X ⟶ X ⊞ (0 : C)) = biprod.inl
  exact (Category.comp_id _).symm.trans (Category.comp_id _)

/-- The left unitor of the binary biproduct: a zero first summand may be deleted. -/
noncomputable def biprodLeftUnitor (X : C) [HasBinaryBiproduct (0 : C) X] : (0 : C) ⊞ X ≅ X where
  hom := biprod.snd
  inv := biprod.inr
  hom_inv_id := by
    refine biprod.hom_ext _ _ ?_ (by simp)
    simpa using ((isZero_zero C).eq_of_tgt 0 biprod.fst)
  inv_hom_id := by simp

/-- The forward map of the left biproduct unitor is the second projection. -/
@[simp]
lemma biprodLeftUnitor_hom (X : C) [HasBinaryBiproduct (0 : C) X] :
    (biprodLeftUnitor X).hom = biprod.snd := by
  change (biprod.snd : (0 : C) ⊞ X ⟶ X) = biprod.snd
  exact (Category.comp_id _).symm.trans (Category.comp_id _)

/-- The inverse map of the left biproduct unitor is the second inclusion. -/
@[simp]
lemma biprodLeftUnitor_inv (X : C) [HasBinaryBiproduct (0 : C) X] :
    (biprodLeftUnitor X).inv = biprod.inr := by
  change (biprod.inr : X ⟶ (0 : C) ⊞ X) = biprod.inr
  exact (Category.comp_id _).symm.trans (Category.comp_id _)

end Unitors

end TauCeti
