/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Opposite

/-!
# Object properties and equivalences

This file contains general lemmas about transporting object properties along equivalences.

## Main declarations

* `TauCeti.ObjectProperty.inverseImage_equivalence_inverseImage`: pulling an
  isomorphism-invariant property backward along both functors of an equivalence recovers it.
-/

public section

namespace TauCeti

open CategoryTheory

universe u₁ v₁ u₂ v₂

/-- Pulling an isomorphism-invariant object property backward along both functors of an
equivalence recovers the original property. -/
theorem ObjectProperty.inverseImage_equivalence_inverseImage
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.inverse).inverseImage e.functor = P := by
  ext X
  exact (P.prop_iff_of_iso (e.unitIso.app X)).symm

end TauCeti
