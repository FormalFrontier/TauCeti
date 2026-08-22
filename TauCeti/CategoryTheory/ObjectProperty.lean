/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# General lemmas on object properties

This file contains general lemmas about object properties: transporting them along equivalences,
and the closure properties they inherit in a preadditive category.

## Main declarations

* `CategoryTheory.ObjectProperty.inverseImage_functor_inverseImage_inverse`: pulling an
  isomorphism-invariant property backward along both functors of an equivalence recovers it.
* `TauCeti.prop_biprod_of_binaryProducts`: in a preadditive category, closure under binary
  products is closure under binary biproducts.
-/

public section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

namespace ObjectProperty

/-- Pulling an isomorphism-invariant object property backward along both functors of an
equivalence recovers the original property. -/
theorem inverseImage_functor_inverseImage_inverse
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.inverse).inverseImage e.functor = P := by
  ext X
  exact (P.prop_iff_of_iso (e.unitIso.app X)).symm

end ObjectProperty

end CategoryTheory

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

/-- An object property closed under binary products in a preadditive category is closed under
binary biproducts. -/
theorem prop_biprod_of_binaryProducts {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (P : ObjectProperty C) [P.IsClosedUnderBinaryProducts] {X Y : C} [HasBinaryBiproduct X Y]
    (hX : P X) (hY : P Y) : P (X ⊞ Y) :=
  P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit X Y) hX hY

end TauCeti
