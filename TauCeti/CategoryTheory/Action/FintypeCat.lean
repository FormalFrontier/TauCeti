/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.FintypeCat

/-!
# Finite `G`-sets, as a subcategory of all `G`-sets and as actions in `FintypeCat`

Mathlib has two descriptions of a finite set with a `G`-action: an object of
`Action FintypeCat G`, an action internal to the category of finite types, and an object of
`Action (Type u) G` whose underlying type happens to be finite. The first is the one carrying the
Galois-category structure of `Mathlib/CategoryTheory/Galois/Examples.lean`, while the second is
what a classification theorem valued in `Action (Type u) G` — such as the classification of
covering spaces by `π₁`-sets — restricts to. This file identifies them.

`FintypeCat` is by definition the full subcategory of `Type u` on the finite types, so the two
categories differ only in how the same data is bracketed: a morphism on either side is an
equivariant map of the underlying types, and both composites are the identity functor on the
nose. The equivalence is therefore built with identity unit and counit.

## Main declarations

* `TauCeti.isFiniteAction`: the property of a `G`-set that its underlying type is finite.
* `TauCeti.FiniteAction`: finite `G`-sets as a full subcategory of all `G`-sets.
* `TauCeti.FiniteAction.toActionFintypeCat` and `TauCeti.FiniteAction.ofActionFintypeCat`: the
  two comparison functors, with `toActionFintypeCat_obj_V`, `toActionFintypeCat_obj_ρ_apply`,
  `toActionFintypeCat_map_hom_apply` and their `ofActionFintypeCat` counterparts computing them
  on underlying types, actions and maps.
* `TauCeti.FiniteAction.equivalenceActionFintypeCat`: **finite `G`-sets are the same thing as
  actions of `G` in the category of finite types.**
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

variable (G : Type v) [Monoid G]

/-- A `G`-set is *finite* when its underlying type is finite. -/
def isFiniteAction : ObjectProperty (Action (Type u) G) :=
  fun A => Finite A.V

variable {G}

/-- Membership in the finiteness property of `G`-sets. -/
@[simp]
theorem isFiniteAction_iff (A : Action (Type u) G) :
    isFiniteAction G A ↔ Finite A.V :=
  Iff.rfl

variable (G)

/-- Finiteness of a `G`-set is preserved by isomorphisms of `G`-sets: an isomorphism is in
particular a bijection of the underlying types. -/
instance : (isFiniteAction.{u} G).IsClosedUnderIsomorphisms where
  of_iso {A _} e h :=
    have : Finite A.V := h
    (isFiniteAction_iff _).2 (Finite.of_equiv A.V ((Action.forget _ G).mapIso e).toEquiv)

/-- Finite `G`-sets, as a full subcategory of all `G`-sets. -/
abbrev FiniteAction : Type _ :=
  (isFiniteAction.{u} G).FullSubcategory

namespace FiniteAction

/-- The fully faithful inclusion of finite `G`-sets into all `G`-sets. -/
abbrev forget : FiniteAction.{u} G ⥤ Action (Type u) G :=
  ObjectProperty.ι _

/-- The inclusion of finite `G`-sets into all `G`-sets is fully faithful. -/
def fullyFaithfulForget : (forget.{u} G).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

variable {G}

/-- Construct a finite `G`-set from a `G`-set with finite underlying type. -/
def mk (A : Action (Type u) G) (hA : isFiniteAction G A) : FiniteAction G :=
  ⟨A, hA⟩

/-- The underlying type of a finite `G`-set is finite. -/
instance finite (A : FiniteAction.{u} G) : Finite A.obj.V :=
  (isFiniteAction_iff _).1 A.property

variable (G)

/-- A finite `G`-set, read as an action of `G` in the category of finite types. -/
def toActionFintypeCat : FiniteAction.{u} G ⥤ Action FintypeCat.{u} G where
  obj A :=
    { V := ⟨A.obj.V, (isFiniteAction_iff _).1 A.property⟩
      ρ :=
        { toFun := fun g => ObjectProperty.homMk (A.obj.ρ g)
          map_one' := by
            apply ObjectProperty.hom_ext
            simp [End.one_def]
          map_mul' := fun g h => by
            apply ObjectProperty.hom_ext
            simp [End.mul_def] } }
  map f :=
    { hom := ObjectProperty.homMk f.hom.hom
      comm := fun g => by
        apply ObjectProperty.hom_ext
        simpa using f.hom.comm g }

/-- An action of `G` in the category of finite types, read as a finite `G`-set. -/
def ofActionFintypeCat : Action FintypeCat.{u} G ⥤ FiniteAction.{u} G :=
  ObjectProperty.lift _ (FintypeCat.incl.mapAction G) fun B => (isFiniteAction_iff _).2 B.V.property

/-- The underlying finite type of a finite `G`-set, read in `FintypeCat`, is its underlying
type. -/
@[simp]
theorem toActionFintypeCat_obj_V (A : FiniteAction.{u} G) :
    ((toActionFintypeCat G).obj A).V.obj = A.obj.V :=
  (rfl)

/-- Reading a finite `G`-set in `FintypeCat` keeps the action of `G`. -/
@[simp]
theorem toActionFintypeCat_obj_ρ_apply (A : FiniteAction.{u} G) (g : G) (x : A.obj.V) :
    cast (toActionFintypeCat_obj_V G A)
        (ConcreteCategory.hom (((toActionFintypeCat G).obj A).ρ g)
          (cast (toActionFintypeCat_obj_V G A).symm x)) =
      A.obj.ρ g x :=
  (rfl)

/-- Reading a map of finite `G`-sets in `FintypeCat` keeps the underlying map. -/
@[simp]
theorem toActionFintypeCat_map_hom_apply {A B : FiniteAction.{u} G} (f : A ⟶ B) (x : A.obj.V) :
    cast (toActionFintypeCat_obj_V G B)
        (ConcreteCategory.hom ((toActionFintypeCat G).map f).hom
          (cast (toActionFintypeCat_obj_V G A).symm x)) =
      f.hom.hom x :=
  (rfl)

/-- The underlying type of an action of `G` in `FintypeCat`, read as a finite `G`-set, is its
underlying finite type. -/
@[simp]
theorem ofActionFintypeCat_obj_obj_V (B : Action FintypeCat.{u} G) :
    ((ofActionFintypeCat G).obj B).obj.V = B.V.obj :=
  (rfl)

/-- Reading an action of `G` in `FintypeCat` as a finite `G`-set keeps the action of `G`. -/
@[simp]
theorem ofActionFintypeCat_obj_obj_ρ_apply (B : Action FintypeCat.{u} G) (g : G) (x : B.V) :
    cast (ofActionFintypeCat_obj_obj_V G B)
        (((ofActionFintypeCat G).obj B).obj.ρ g
          (cast (ofActionFintypeCat_obj_obj_V G B).symm x)) =
      ConcreteCategory.hom (B.ρ g) x :=
  (rfl)

/-- Reading a map of actions of `G` in `FintypeCat` as a map of finite `G`-sets keeps the
underlying map. -/
@[simp]
theorem ofActionFintypeCat_map_hom_hom_apply {B C : Action FintypeCat.{u} G} (f : B ⟶ C)
    (x : B.V) :
    cast (ofActionFintypeCat_obj_obj_V G C)
        (((ofActionFintypeCat G).map f).hom.hom
          (cast (ofActionFintypeCat_obj_obj_V G B).symm x)) =
      ConcreteCategory.hom f.hom x :=
  (rfl)

/-- **Finite `G`-sets are the same thing as actions of `G` in the category of finite types.**

Both composites are the identity functor on the nose, since `FintypeCat` is by definition the
full subcategory of `Type u` on the finite types. -/
def equivalenceActionFintypeCat : FiniteAction.{u} G ≌ Action FintypeCat.{u} G where
  functor := toActionFintypeCat G
  inverse := ofActionFintypeCat G
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
theorem equivalenceActionFintypeCat_functor :
    (equivalenceActionFintypeCat.{u} G).functor = toActionFintypeCat G :=
  (rfl)

@[simp]
theorem equivalenceActionFintypeCat_inverse :
    (equivalenceActionFintypeCat.{u} G).inverse = ofActionFintypeCat G :=
  (rfl)

end FiniteAction

end TauCeti
