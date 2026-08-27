/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Object properties: transport along equivalences, and closure properties

This file contains general lemmas about object properties: transporting them along an
equivalence, comparing Mathlib's closure type classes with one another in the presence of a
zero object and of binary biproducts, smallness of full subcategories, and additivity of inclusions
between full subcategories.

## Main declarations

* `CategoryTheory.ObjectProperty.inverseImage_functor_inverseImage_inverse`: pulling an
  isomorphism-invariant property backward along both functors of an equivalence recovers it.
* `CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_containsZero`: a property holding
  for a zero object and closed under binary products is closed under isomorphisms.
* `CategoryTheory.ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod`: for a replete
  property in a category with binary biproducts, closure under binary products only has to be
  checked on biproducts.
* `CategoryTheory.ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts`: a property closed
  under binary products holds for binary biproducts, with `X ⊞ Y` as the syntactic form of the
  conclusion.
* `CategoryTheory.ObjectProperty.essentiallySmall_of_ambient`: every property in an essentially
  small category is essentially small.
* `CategoryTheory.ObjectProperty.ιOfLE_additive`: the inclusion of a smaller property into a larger
  one is additive.
-/

public section

universe w u₁ v₁ u₂ v₂

namespace CategoryTheory

open Limits

namespace ObjectProperty

/-- Pulling an isomorphism-invariant object property backward along both functors of an
equivalence recovers the original property. -/
theorem inverseImage_functor_inverseImage_inverse
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.inverse).inverseImage e.functor = P := by
  ext X
  exact (P.prop_iff_of_iso (e.unitIso.app X)).symm

/-- **A property holding for a zero object and closed under binary products is closed under
isomorphisms.** An isomorphism `e : X ≅ Y` exhibits `Y` as a product of a zero object with `X`,
the two projections being the zero morphism and `e.inv`.

Mathlib's `CategoryTheory.ObjectProperty.IsClosedUnderBinaryProducts.closedUnderIsomorphisms` is
the same argument run on a terminal object, but it assumes closure under the empty limit, which
`CategoryTheory.ObjectProperty.ContainsZero` — the property for *one* zero object — does not
supply before repleteness is known. -/
theorem isClosedUnderIsomorphisms_of_containsZero {C : Type u₁} [Category.{v₁} C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨Z, hZ, hZP⟩ := P.exists_prop_of_containsZero
    let B : BinaryFan Z X := BinaryFan.mk (hZ.from_ Y) e.inv
    have hB : IsLimit B := BinaryFan.IsLimit.mk B (fun _ g => g ≫ e.hom)
      (fun _ _ => hZ.eq_of_tgt _ _)
      (fun _ _ => by simp [B])
      (fun _ _ _ _ hg => by simpa [B] using congrArg (fun k => k ≫ e.hom) hg)
    exact P.prop_of_isLimit_binaryFan hB hZP hX

/-- **For a replete property, closure under binary products only has to be checked on
biproducts**, since in a category with binary biproducts every binary product is one. -/
theorem isClosedUnderBinaryProducts_of_prop_biprod {C : Type u₁} [Category.{v₁} C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (h : ∀ X Y : C, P X → P Y → P (X ⊞ Y)) :
    P.IsClosedUnderBinaryProducts := by
  refine IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  refine P.prop_of_iso ?_ (h _ _ (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))
  exact (biprod.isoProd _ _).trans (HasLimit.isoOfNatIso (diagramIsoPair F)).symm

/-- **A property closed under binary products holds for binary biproducts.** In a category with
binary biproducts the biproduct is a binary product, so this is
`CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan` applied to
`CategoryTheory.Limits.BinaryBiproduct.isLimit`; naming it keeps the index of the conclusion
syntactically `X ⊞ Y`, which matters when the conclusion is the type index of a dependent
family. -/
theorem prop_biprod_of_isClosedUnderBinaryProducts {C : Type u₁} [Category.{v₁} C]
    [HasZeroMorphisms C] (P : ObjectProperty C) [P.IsClosedUnderBinaryProducts]
    {X Y : C} [HasBinaryBiproduct X Y] (hX : P X) (hY : P Y) : P (X ⊞ Y) :=
  P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit X Y) hX hY

/-- Every object property in an essentially small category is essentially small. This supplies
the smallness instance for its full subcategory through Mathlib's object-property API. -/
instance essentiallySmall_of_ambient {C : Type u₁} [Category.{v₁} C]
    [CategoryTheory.EssentiallySmall.{w} C] (P : ObjectProperty C) :
    ObjectProperty.EssentiallySmall.{w} P :=
  ObjectProperty.EssentiallySmall.of_le.{w} (Q := (⊤ : ObjectProperty C)) le_top

/-- The inclusion of a smaller object property into a larger one is an additive functor: both
categories carry the addition of the ambient one. -/
instance ιOfLE_additive {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {P P' : ObjectProperty C} (h : P ≤ P') : (ObjectProperty.ιOfLE h).Additive where
  map_add := rfl

end ObjectProperty

end CategoryTheory
