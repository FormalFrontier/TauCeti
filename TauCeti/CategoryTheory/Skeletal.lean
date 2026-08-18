/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Skeletal

/-!
# Eliminating and lifting from a category skeleton

This file supplies the constructor-facing API for `CategoryTheory.Skeleton`: an eliminator, a lift
of isomorphism-invariant functions, and comparison of classes in a full subcategory through
isomorphisms of the ambient category.
-/

public section

namespace CategoryTheory

attribute [local instance] isIsomorphicSetoid

universe u v w

namespace ObjectProperty

/-- Two objects of a full subcategory define the same point of its skeleton exactly when the
underlying objects are isomorphic. -/
theorem toSkeleton_eq_toSkeleton_iff_nonempty_iso {C : Type u} [Category.{v} C]
    (P : ObjectProperty C) {X Y : C} (hX : P X) (hY : P Y) :
    toSkeleton (⟨X, hX⟩ : P.FullSubcategory) = toSkeleton ⟨Y, hY⟩ ↔ Nonempty (X ≅ Y) := by
  rw [CategoryTheory.toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨P.ι.mapIso e⟩, fun ⟨e⟩ ↦ ⟨ObjectProperty.isoMk _ e⟩⟩

end ObjectProperty

namespace Skeleton

/-- To prove a property of every object-isomorphism class, it suffices to prove it on the class of
each object. -/
@[elab_as_elim]
theorem ind {C : Type u} [Category.{v} C] {motive : Skeleton C → Prop}
    (h : ∀ X : C, motive (toSkeleton X)) (c : Skeleton C) : motive c := by
  exact Quotient.ind h c

/-- Define a function on object-isomorphism classes from an isomorphism-invariant function on
objects. -/
noncomputable def lift {C : Type u} [Category.{v} C] {α : Sort w} (f : C → α)
    (h : ∀ X Y : C, Nonempty (X ≅ Y) → f X = f Y) : Skeleton C → α :=
  Quotient.lift f fun X Y e ↦ h X Y e

@[simp]
theorem lift_toSkeleton {C : Type u} [Category.{v} C] {α : Sort w} (f : C → α)
    (h : ∀ X Y : C, Nonempty (X ≅ Y) → f X = f Y) (X : C) :
    lift f h (toSkeleton X) = f X := by
  simp [lift]

end Skeleton

end CategoryTheory
