/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Cat

/-!
# Preadditive structure on comodule categories

This file records the additive-group structure on morphisms of right comodules over a
coalgebra over a commutative ring, and uses it to make the bundled comodule category
preadditive.

The semiring-level files already show that comodule morphisms are closed under zero,
addition, scalar multiplication, and finite sums. Over a ring, every semimodule is an
additive group by `Module.addCommMonoidToAddCommGroup`; the same pointwise operations also
give negatives and subtraction of comodule morphisms. This is the categorical additive
infrastructure needed before the reductive-groups roadmap's finite-dimensional comodule
representation category can be developed.

## Main declarations

* `TauCeti.Comodule.Hom.instAddCommGroup`: pointwise additive-group structure on comodule
  morphisms over a commutative ring.
* `TauCeti.ComoduleCat.homAddCommGroup`: additive-group structure on bundled comodule
  morphisms over a commutative ring.
* `TauCeti.ComoduleCat.preadditive`: `ComoduleCat R C` is preadditive over a commutative
  ring `R`.

## References

This supplies a prerequisite for
`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1 target "Comodules over a coalgebra/Hopf
algebra": the finite-dimensional comodule representation category should be an additive
category before tensor products, duals, and Tannakian structure are built on top.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommRing R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

namespace Hom

/-- Comodule morphisms over a commutative ring form an additive commutative group under
pointwise operations. -/
instance instAddCommGroup : AddCommGroup (Hom R C M N) :=
  Module.addCommMonoidToAddCommGroup R

/-- Negation of comodule morphisms is negation of the underlying linear maps. -/
@[simp]
theorem neg_toLinearMap (f : Hom R C M N) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (-f).toLinearMap = -f.toLinearMap :=
  rfl

/-- Subtraction of comodule morphisms is subtraction of the underlying linear maps. -/
@[simp]
theorem sub_toLinearMap (f g : Hom R C M N) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap :=
  rfl

/-- Integer scalar multiplication of comodule morphisms is integer scalar multiplication of
the underlying linear maps. -/
@[simp]
theorem zsmul_toLinearMap (z : ℤ) (f : Hom R C M N) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (z • f).toLinearMap = z • f.toLinearMap :=
  rfl

/-- Negation of comodule morphisms is pointwise negation. -/
@[simp]
theorem neg_apply (f : Hom R C M N) (m : M) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (-f) m = -f m :=
  rfl

/-- Subtraction of comodule morphisms is pointwise subtraction. -/
@[simp]
theorem sub_apply (f g : Hom R C M N) (m : M) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (f - g) m = f m - g m :=
  rfl

/-- Integer scalar multiplication of comodule morphisms is pointwise. -/
@[simp]
theorem zsmul_apply (z : ℤ) (f : Hom R C M N) (m : M) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (z • f) m = z • f m :=
  rfl

section Comp

variable {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]

/-- Composition of comodule morphisms is compatible with negation in the left argument. -/
@[simp]
theorem neg_comp (g : Hom R C N P) (f : Hom R C M N) :
    comp (-g) f = -comp g f := by
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  ext m
  simp [comp]

/-- Composition of comodule morphisms is compatible with negation in the right argument. -/
@[simp]
theorem comp_neg (g : Hom R C N P) (f : Hom R C M N) :
    comp g (-f) = -comp g f := by
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  ext m
  exact map_neg g.toLinearMap (f m)

/-- Composition of comodule morphisms is subtractive in the left argument. -/
@[simp]
theorem sub_comp (g h : Hom R C N P) (f : Hom R C M N) :
    comp (g - h) f = comp g f - comp h f := by
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  ext m
  simp [comp, sub_eq_add_neg]

/-- Composition of comodule morphisms is subtractive in the right argument. -/
@[simp]
theorem comp_sub (g : Hom R C N P) (f h : Hom R C M N) :
    comp g (f - h) = comp g f - comp g h := by
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  ext m
  exact map_sub g.toLinearMap (f m) (h m)

end Comp

end Hom

end Comodule

namespace ComoduleCat

universe u v w

variable (R : Type u) [CommRing R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Categorical morphisms form an additive commutative group over a commutative ring. -/
instance homAddCommGroup (M N : ComoduleCat.{u, v, w} R C) : AddCommGroup (M ⟶ N) :=
  inferInstanceAs (AddCommGroup (Comodule.Hom R C M N))

/-- Negation of morphisms is negation of the underlying linear maps. -/
@[simp]
theorem toLinearMap_neg {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (-f).toLinearMap = -f.toLinearMap :=
  Comodule.Hom.neg_toLinearMap f

/-- Subtraction of morphisms is subtraction of the underlying linear maps. -/
@[simp]
theorem toLinearMap_sub {M N : ComoduleCat.{u, v, w} R C} (f g : M ⟶ N) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap :=
  Comodule.Hom.sub_toLinearMap f g

/-- Integer scalar multiplication of morphisms is integer scalar multiplication of the
underlying linear maps. -/
@[simp]
theorem toLinearMap_zsmul {M N : ComoduleCat.{u, v, w} R C} (z : ℤ) (f : M ⟶ N) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (z • f).toLinearMap = z • f.toLinearMap :=
  Comodule.Hom.zsmul_toLinearMap z f

/-- Negation of morphisms acts by pointwise negation. -/
@[simp]
theorem neg_apply {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) (m : M) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (-f) m = -f m :=
  Comodule.Hom.neg_apply f m

/-- Subtraction of morphisms acts by pointwise subtraction. -/
@[simp]
theorem sub_apply {M N : ComoduleCat.{u, v, w} R C} (f g : M ⟶ N) (m : M) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (f - g) m = f m - g m :=
  Comodule.Hom.sub_apply f g m

/-- Integer scalar multiplication of morphisms acts pointwise. -/
@[simp]
theorem zsmul_apply {M N : ComoduleCat.{u, v, w} R C} (z : ℤ) (f : M ⟶ N) (m : M) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    (z • f) m = z • f m :=
  Comodule.Hom.zsmul_apply z f m

/-- The category of right comodules over a coalgebra over a commutative ring is
preadditive. -/
instance preadditive : Preadditive (ComoduleCat.{u, v, w} R C) where
  homGroup M N := by
    letI : AddCommGroup C := Module.addCommMonoidToAddCommGroup R
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    exact inferInstanceAs (AddCommGroup (Comodule.Hom R C M N))
  add_comp M N P f g h := by
    let : AddCommGroup C := Module.addCommMonoidToAddCommGroup R
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
    exact Comodule.Hom.comp_add (R := R) (C := C) h f g
  comp_add M N P f g h := by
    let : AddCommGroup C := Module.addCommMonoidToAddCommGroup R
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
    exact Comodule.Hom.add_comp (R := R) (C := C) g h f

end ComoduleCat

end TauCeti
