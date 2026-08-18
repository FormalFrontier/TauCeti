/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Skeletal

/-!
# Comparing objects in a category skeleton

This file compares classes in the skeleton of a full subcategory through isomorphisms of the
ambient category.
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
