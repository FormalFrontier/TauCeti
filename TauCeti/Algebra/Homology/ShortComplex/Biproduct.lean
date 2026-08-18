/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Binary biproducts of short complexes

Two short complexes in a category with zero morphisms have a componentwise binary direct sum,
provided the three relevant binary biproducts exist. This file constructs it and records the
projection lemmas identifying its objects and maps.

## Main definitions

* `TauCeti.shortComplexBiprod`: the componentwise binary direct sum of two short complexes.

## Implementation notes

`shortComplexBiprod` is `@[expose]`d so that its objects are definitionally the corresponding
biproducts outside this file. Without that, the type of `(shortComplexBiprod S₁ S₂).f` could not
be seen to be `S₁.X₁ ⊞ S₂.X₁ ⟶ S₁.X₂ ⊞ S₂.X₂`, and the projection lemmas for the two maps would
have to be stated with a heterogeneous equality.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The two maps in the componentwise biproduct of short complexes have zero composite. -/
theorem shortComplexBiprod_zero (S₁ S₂ : ShortComplex C)
    [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] :
    biprod.map S₁.f S₂.f ≫ biprod.map S₁.g S₂.g = 0 := by
  ext <;> simp [reassoc_of% S₁.zero, reassoc_of% S₂.zero]

/-- The componentwise binary direct sum of two short complexes. -/
@[expose] noncomputable def shortComplexBiprod (S₁ S₂ : ShortComplex C)
    [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] : ShortComplex C :=
  ShortComplex.mk (biprod.map S₁.f S₂.f) (biprod.map S₁.g S₂.g)
    (shortComplexBiprod_zero S₁ S₂)

/-- The left object of the componentwise biproduct of two short complexes. -/
@[simp]
theorem shortComplexBiprod_X₁ (S₁ S₂ : ShortComplex C)
    [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] :
    (shortComplexBiprod S₁ S₂).X₁ = (S₁.X₁ ⊞ S₂.X₁) := (rfl)

/-- The middle object of the componentwise biproduct of two short complexes. -/
@[simp]
theorem shortComplexBiprod_X₂ (S₁ S₂ : ShortComplex C)
    [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] :
    (shortComplexBiprod S₁ S₂).X₂ = (S₁.X₂ ⊞ S₂.X₂) := (rfl)

/-- The right object of the componentwise biproduct of two short complexes. -/
@[simp]
theorem shortComplexBiprod_X₃ (S₁ S₂ : ShortComplex C)
    [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] :
    (shortComplexBiprod S₁ S₂).X₃ = (S₁.X₃ ⊞ S₂.X₃) := (rfl)

/-- The first map of the componentwise biproduct of two short complexes. -/
@[simp]
theorem shortComplexBiprod_f (S₁ S₂ : ShortComplex C)
    [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] :
    (shortComplexBiprod S₁ S₂).f = biprod.map S₁.f S₂.f := (rfl)

/-- The second map of the componentwise biproduct of two short complexes. -/
@[simp]
theorem shortComplexBiprod_g (S₁ S₂ : ShortComplex C)
    [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] :
    (shortComplexBiprod S₁ S₂).g = biprod.map S₁.g S₂.g := (rfl)

end TauCeti
