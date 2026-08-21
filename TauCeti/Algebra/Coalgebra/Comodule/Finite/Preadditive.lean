/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Preadditive

/-!
# Preadditive structure on finitely generated comodules

This file makes the preadditive structure on the category of finitely generated right
comodules over a coalgebra over a commutative ring available from a finite-comodule import.
The category is a full subcategory of all comodules, so Mathlib transfers the preadditive
structure from `ComoduleCat`.

It also records concrete simp lemmas computing the zero, addition, negation, and subtraction of
finitely generated comodule morphisms through the underlying ambient comodule morphism `.hom`,
and pointwise on elements, so downstream code never has to unfold the full-subcategory transfer.

This is a small Layer 1 prerequisite for the reductive-groups roadmap's finite-dimensional
representation category: additive hom-sets are needed before tensor products, duals, and
Tannakian reconstruction can be built on finitely generated comodules.

## Main declarations

* `TauCeti.FGComoduleCat.hom_zero`, `hom_add`, `hom_neg`, `hom_sub`: the additive-group
  operations on finitely generated comodule morphisms agree with those of the ambient
  `ComoduleCat` morphism underneath.
* `TauCeti.FGComoduleCat.zero_apply`, `add_apply`, `neg_apply`, `sub_apply`: the same
  operations computed pointwise on elements.

## References

This supplies additive-category bookkeeping for
`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1 target "Comodules over a coalgebra/Hopf
algebra": the finite-dimensional comodule category should have additive hom-sets before the
rigid monoidal representation category is developed. The transfer mechanism is Mathlib's
`ObjectProperty.FullSubcategory` preadditive instance.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M N : FGComoduleCat.{u, v, w} R C}

/-- The ambient comodule morphism underlying the zero morphism is the zero morphism. -/
@[simp]
theorem hom_zero : (0 : M ⟶ N).hom = 0 :=
  rfl

/-- The ambient comodule morphism underlying a sum is the sum of the underlying morphisms. -/
@[simp]
theorem hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom :=
  rfl

/-- The ambient comodule morphism underlying a negation is the negation of the underlying
morphism. -/
@[simp]
theorem hom_neg (f : M ⟶ N) : (-f).hom = -f.hom :=
  rfl

/-- The ambient comodule morphism underlying a difference is the difference of the underlying
morphisms. -/
@[simp]
theorem hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom :=
  rfl

/-- The zero morphism acts as the zero function. -/
@[simp]
theorem zero_apply (m : M) : (0 : M ⟶ N) m = 0 :=
  rfl

/-- Addition of morphisms acts by pointwise addition. -/
@[simp]
theorem add_apply (f g : M ⟶ N) (m : M) : (f + g) m = f m + g m :=
  rfl

/-- Negation of morphisms acts by pointwise negation. -/
@[simp]
theorem neg_apply (f : M ⟶ N) (m : M) : (-f) m = -f m :=
  rfl

/-- Subtraction of morphisms acts by pointwise subtraction. -/
@[simp]
theorem sub_apply (f g : M ⟶ N) (m : M) : (f - g) m = f m - g m :=
  rfl

end FGComoduleCat

end TauCeti
