/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.GroupTheory.Finiteness

/-!
# Finitely generated commutative groups

This file packages finitely generated commutative groups as a full subcategory of
`CommGrpCat`.

## Main declarations

* `TauCeti.CommGrpCat.isFG`: the object property of being finitely generated.
* `TauCeti.FGCommGrpCat`: the category of finitely generated commutative groups.
-/

public section

open CategoryTheory

namespace TauCeti

universe v

namespace CommGrpCat

/-- The object property of being a finitely generated commutative group. -/
def isFG : ObjectProperty CommGrpCat.{v} :=
  fun G => Group.FG G

/-- Membership in the finitely generated commutative-group object property. -/
@[simp]
theorem isFG_iff (G : CommGrpCat.{v}) :
    isFG G ↔ Group.FG G :=
  Iff.rfl

end CommGrpCat

/-- The category of finitely generated commutative groups. -/
abbrev FGCommGrpCat :=
  CommGrpCat.isFG.FullSubcategory

namespace FGCommGrpCat

/-- The underlying type of a finitely generated commutative group. -/
@[expose, reducible]
def carrier (G : FGCommGrpCat.{v}) : Type v :=
  G.obj

/-- Objects of `FGCommGrpCat` coerce to their underlying type. -/
instance : CoeSort FGCommGrpCat.{v} (Type v) :=
  ⟨carrier⟩

attribute [coe] carrier

/-- An object of `FGCommGrpCat` inherits the commutative-group structure of its
underlying group. -/
instance (G : FGCommGrpCat.{v}) : CommGroup G :=
  inferInstanceAs (CommGroup G.obj)

/-- The underlying group of an object of `FGCommGrpCat` is finitely generated. -/
instance (G : FGCommGrpCat.{v}) : Group.FG G :=
  G.property

/-- Construct an object of `FGCommGrpCat` from a finitely generated commutative group. -/
abbrev of (G : Type v) [CommGroup G] [Group.FG G] : FGCommGrpCat.{v} :=
  ⟨CommGrpCat.of G, (CommGrpCat.isFG_iff _).2 inferInstance⟩

/-- Lift a group homomorphism between finitely generated commutative groups to
`FGCommGrpCat`. -/
abbrev ofHom {G H : Type v} [CommGroup G] [Group.FG G] [CommGroup H] [Group.FG H]
    (φ : G →* H) : of G ⟶ of H :=
  ObjectProperty.homMk (CommGrpCat.ofHom φ)

/-- The group homomorphism underlying a morphism in `FGCommGrpCat`. -/
abbrev toMonoidHom {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) : G →* H :=
  φ.hom.hom

@[simp]
theorem ofHom_toMonoidHom {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) :
    ofHom (toMonoidHom φ) = φ :=
  rfl

@[simp]
theorem toMonoidHom_ofHom {G H : Type v} [CommGroup G] [Group.FG G]
    [CommGroup H] [Group.FG H] (φ : G →* H) :
    toMonoidHom (ofHom φ) = φ :=
  rfl

/-- Two morphisms in `FGCommGrpCat` are equal when their underlying group homomorphisms
are equal. -/
@[ext]
theorem hom_ext {G H : FGCommGrpCat.{v}} {φ ψ : G ⟶ H}
    (h : toMonoidHom φ = toMonoidHom ψ) : φ = ψ :=
  ObjectProperty.hom_ext (P := CommGrpCat.isFG) (CommGrpCat.hom_ext h)

@[simp]
theorem toMonoidHom_id {G : FGCommGrpCat.{v}} :
    toMonoidHom (𝟙 G) = MonoidHom.id G :=
  rfl

@[simp]
theorem toMonoidHom_comp {G H K : FGCommGrpCat.{v}} (φ : G ⟶ H) (ψ : H ⟶ K) :
    toMonoidHom (φ ≫ ψ) = (toMonoidHom ψ).comp (toMonoidHom φ) :=
  rfl

end FGCommGrpCat

end TauCeti
