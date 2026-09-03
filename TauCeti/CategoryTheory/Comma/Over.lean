/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Isomorphisms of objects over a base

An isomorphism in `Over X` is an isomorphism of the underlying objects. Mathlib records this
for comma categories (`CategoryTheory.Comma.instIsIsoLeft`) and for arrow categories
(`CategoryTheory.Arrow.isIso_left`), but `Over X` is a `def` rather than an abbreviation for
a comma category, so instance search does not see through it to the comma statement. This file
supplies the missing `Over` form, which lets `infer_instance` discharge `IsIso φ.left` goals
that otherwise have to name the forgetful functor by hand.

## Main declarations

* `CategoryTheory.Over.isIso_left`: the underlying morphism of an isomorphism over a base is
  an isomorphism.
-/

public section

universe v u

namespace CategoryTheory

namespace Over

/-- The underlying morphism of an isomorphism in `Over X` is an isomorphism. -/
instance isIso_left {T : Type u} [Category.{v} T] {X : T} {f g : Over X} (φ : f ⟶ g)
    [IsIso φ] : IsIso φ.left :=
  (Over.forget X).map_isIso φ

end Over

end CategoryTheory
