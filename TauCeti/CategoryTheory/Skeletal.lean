/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Skeletal

/-!
# Comparing objects in the skeleton of a full subcategory

Mathlib's `CategoryTheory.toSkeleton_eq_toSkeleton_iff` says that two objects have the same class
in `CategoryTheory.Skeleton C` exactly when they are isomorphic *in `C`*. When `C` is a full
subcategory `P.FullSubcategory`, that is an isomorphism of the bundled pairs, whereas a consumer
starts and ends with objects of the ambient category and wants an isomorphism there. The gap is
only bookkeeping -- the inclusion `ObjectProperty.ι` is full and faithful, so the two notions of
isomorphism correspond -- but it has to be crossed every time the skeleton of a full subcategory is
used as a type of isomorphism classes. This file crosses it once.

Its consumer is `TauCeti.SimpleFDRepClasses.mk_eq_mk_iff`, which says that two simple objects of
`FDRep k G` have the same isomorphism class exactly when they are isomorphic in `FDRep k G`, and
through it every classification statement valued in `TauCeti.SimpleFDRepClasses`.

## Main results

* `CategoryTheory.ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso`: two objects of a full
  subcategory have the same class in its skeleton exactly when they are isomorphic in the ambient
  category.
-/

public section

namespace CategoryTheory

attribute [local instance] isIsomorphicSetoid

universe u v

namespace ObjectProperty

/-- Two objects of a full subcategory define the same point of its skeleton exactly when the
underlying objects are isomorphic. -/
theorem toSkeleton_eq_toSkeleton_iff_nonempty_iso {C : Type u} [Category.{v} C]
    (P : ObjectProperty C) {X Y : C} (hX : P X) (hY : P Y) :
    toSkeleton (⟨X, hX⟩ : P.FullSubcategory) = toSkeleton ⟨Y, hY⟩ ↔ Nonempty (X ≅ Y) := by
  rw [CategoryTheory.toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨P.ι.mapIso e⟩, fun ⟨e⟩ ↦ ⟨ObjectProperty.isoMk _ e⟩⟩

end ObjectProperty

end CategoryTheory
