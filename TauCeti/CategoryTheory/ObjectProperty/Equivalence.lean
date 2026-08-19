/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Opposite

/-!
# Object properties and equivalences

This file records compatibility results between equivalences and object properties that are
useful when restricting an equivalence to full subcategories.

## Main declarations

* `CategoryTheory.ObjectProperty.inverseImage_inverse_inverseImage_functor`: pulling an
  isomorphism-closed property back along both sides of an equivalence recovers the property.
* `CategoryTheory.Equivalence.congrFullSubcategoryOp`: restriction of an equivalence from an
  opposite category to full subcategories.
* `CategoryTheory.Equivalence.congrFullSubcategoryFunctorCompιIso`: the inclusion-functor
  interface for restricting an equivalence from an opposite category to full subcategories.
-/

public section

namespace CategoryTheory

universe v v' u u'

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Pulling an isomorphism-closed object property back along the inverse and then the functor of
an equivalence recovers the original property. -/
lemma inverseImage_inverse_inverseImage_functor
    (e : C ≌ D) (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    (P.inverseImage e.inverse).inverseImage e.functor = P := by
  ext X
  exact (P.prop_iff_of_iso (e.unitIso.app X)).symm

end ObjectProperty

namespace Equivalence

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Restrict an equivalence from an opposite category to full subcategories, presenting the
source as the opposite of the full subcategory of the original category. -/
noncomputable def congrFullSubcategoryOp
    (e : Cᵒᵖ ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    [Q.IsClosedUnderIsomorphisms] (h : Q.inverseImage e.functor = P.op) :
    P.FullSubcategoryᵒᵖ ≌ Q.FullSubcategory :=
  (ObjectProperty.opEquivalence P).symm.trans (e.congrFullSubcategory h)

/-- Restricting an equivalence from an opposite category to full subcategories and then including
the target is naturally isomorphic to first including the source and then applying the original
equivalence. -/
noncomputable def congrFullSubcategoryFunctorCompιIso
    (e : Cᵒᵖ ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    [Q.IsClosedUnderIsomorphisms] (h : Q.inverseImage e.functor = P.op) :
    (e.congrFullSubcategoryOp P Q h).functor ⋙ Q.ι ≅ P.ι.op ⋙ e.functor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.opEquivalence P).symm.functor
      (Q.liftCompιIso (P.op.ι ⋙ e.functor) _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (P.op.liftCompιIso P.ι.op (fun X => X.unop.property)) e.functor

end Equivalence

end CategoryTheory
