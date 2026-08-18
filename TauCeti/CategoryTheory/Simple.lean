/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Simple

/-!
# Simple objects as an isomorphism-closed property

Simplicity is invariant under isomorphism, so simple objects define an isomorphism-closed full
subcategory in any category with zero morphisms.
-/

public section

namespace CategoryTheory

universe u v

/-- Simplicity is preserved under isomorphism, so simple objects form an isomorphism-closed full
subcategory. -/
instance simple_isClosedUnderIsomorphisms {C : Type u} [Category.{v} C]
    [Limits.HasZeroMorphisms C] :
    ObjectProperty.IsClosedUnderIsomorphisms (Simple : ObjectProperty C) where
  of_iso e h := by
    let _ := h
    exact Simple.of_iso e.symm

end CategoryTheory
