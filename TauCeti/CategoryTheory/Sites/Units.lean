/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The sheaf of units

This file constructs the sheaf of units of a sheaf of commutative rings. We regard the
multiplicative group of units additively, so that the result takes values in `AddCommGrpCat` and
can be used with kernels and cokernels in the abelian category of sheaves of abelian groups.

The construction is pointwise: the units functor is a right adjoint and therefore preserves the
limits in the sheaf condition. Thus a sheaf of commutative rings `F` gives a sheaf whose sections
over `U` are `Additive (F(U)ˣ)`.

This is the categorical input for the Cartier-divisor sheaf
`𝒦_X^× / 𝒪_X^×` in `TauCeti/AlgebraicGeometry/CartierDivisor/Basic.lean`. No formalization is
vendored; the construction composes Mathlib's `CommMonCat.units`, the multiplicative-to-additive
equivalence, and `CategoryTheory.sheafCompose`.
-/

public section

open CategoryTheory

universe u v

namespace CommRingCat

/-- The functor from commutative rings to their groups of units, written additively. -/
abbrev additiveUnits : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ commGroupAddCommGroupEquivalence.functor

end CommRingCat

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Taking the units of a sheaf of commutative rings, written additively. -/
noncomputable abbrev additiveUnitsFunctor :
    Sheaf J CommRingCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafCompose J CommRingCat.additiveUnits

/-- The sections of the additive units sheaf are the units of the original ring of sections. -/
@[simp]
lemma additiveUnitsFunctor_obj_obj (F : Sheaf J CommRingCat.{u}) (U : Cᵒᵖ) :
    ((additiveUnitsFunctor J).obj F).obj.obj U =
      AddCommGrpCat.of (Additive ((F.obj.obj U : CommRingCat.{u})ˣ)) :=
  rfl

/-- A morphism of additive units sheaves acts by applying the original ring morphism to a unit. -/
@[simp]
lemma additiveUnitsFunctor_map_app_apply {F G : Sheaf J CommRingCat.{u}} (f : F ⟶ G)
    (U : Cᵒᵖ) (x : Additive ((F.obj.obj U : CommRingCat.{u})ˣ)) :
    (@AddCommGrpCat.Hom.hom
      (AddCommGrpCat.of (Additive ((F.obj.obj U : CommRingCat.{u})ˣ)))
      (AddCommGrpCat.of (Additive ((G.obj.obj U : CommRingCat.{u})ˣ)))
      (((additiveUnitsFunctor J).map f).hom.app U)) x =
      Additive.ofMul (Units.map (f.hom.app U).hom.toMonoidHom (Additive.toMul x)) :=
  rfl

end CategoryTheory.Sheaf
