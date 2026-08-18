/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Skeletal
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Simple.Basic
public import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-!
# The isomorphism classes of simple objects of `FDRep k G`

A classification of representations is a bijection onto *isomorphism classes*, so it needs a type
of them. For abstract simple modules there is none, since they range over every universe, and
`TauCeti.SimpleSubmoduleClasses` exists to stand in for one: it is the isomorphism classes of
simple *submodules* of a fixed module, which over a semisimple ring realizes every isomorphism
class of simple modules. The objects of `FDRep k G` need no such device, because they already form
a type, and Mathlib already quotients the objects of a category by isomorphism:
`CategoryTheory.Skeleton`. `TauCeti.SimpleFDRepClasses` is that skeleton, taken of the full
subcategory of simple objects, and its namespace supplies the constructor, comparison, eliminator,
and lift that consumers need.

`TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses` compares it with the module-level quotient
over a semisimple group algebra, sending a simple object to the isomorphism class of the
`k[G]`-module it carries. It is what makes a categorical classification and a module-level
classification of the same group two readings of one bijection rather than two unrelated
bijections; see `TauCeti.coe_simpleFDRepClassesEquivSimpleModuleClasses` for the symmetric group.

## Main results

* `TauCeti.SimpleFDRepClasses`: the isomorphism classes of simple objects of `FDRep k G`.
* `TauCeti.SimpleFDRepClasses.mk_eq_mk_iff`: two simple objects have the same class exactly when
  they are isomorphic in `FDRep k G`.
* `TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses`: over a semisimple group algebra, the
  isomorphism class of the `k[G]`-module a simple object carries.
-/

public section

open CategoryTheory

attribute [local instance] isIsomorphicSetoid

namespace CategoryTheory.ObjectProperty

/-- Two objects of a full subcategory define the same point of its skeleton exactly when the
underlying objects are isomorphic. -/
theorem toSkeleton_eq_toSkeleton_iff_nonempty_iso {C : Type*} [Category C]
    (P : ObjectProperty C) {X Y : C} (hX : P X) (hY : P Y) :
    toSkeleton (⟨X, hX⟩ : P.FullSubcategory) = toSkeleton ⟨Y, hY⟩ ↔ Nonempty (X ≅ Y) := by
  rw [CategoryTheory.toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨P.ι.mapIso e⟩, fun ⟨e⟩ ↦ ⟨ObjectProperty.isoMk _ e⟩⟩

end CategoryTheory.ObjectProperty

namespace CategoryTheory

universe u v w

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

/-- Simplicity is preserved under isomorphism, so simple objects form an isomorphism-closed full
subcategory. -/
instance simple_isClosedUnderIsomorphisms {C : Type u} [Category.{v} C]
    [Limits.HasZeroMorphisms C] :
    ObjectProperty.IsClosedUnderIsomorphisms (Simple : ObjectProperty C) where
  of_iso e h := by
    let _ := h
    exact Simple.of_iso e.symm

end CategoryTheory

namespace TauCeti

open scoped MonoidAlgebra

universe u v w

section Ring

variable (k : Type u) (G : Type v) [Ring k] [Monoid G]

/-- **The isomorphism classes of simple objects of `FDRep k G`**: the skeleton of the full
subcategory they span. -/
abbrev SimpleFDRepClasses : Type _ :=
  Skeleton (ObjectProperty.FullSubcategory (Simple : ObjectProperty (FDRep k G)))

variable {k G}

namespace SimpleFDRepClasses

/-- The isomorphism class of a simple object of `FDRep k G`. -/
def mk (X : FDRep k G) [Simple X] : SimpleFDRepClasses k G :=
  toSkeleton (⟨X, inferInstance⟩ :
    ObjectProperty.FullSubcategory (Simple : ObjectProperty (FDRep k G)))

/-- Two simple objects have the same class exactly when they are isomorphic. -/
@[simp]
theorem mk_eq_mk_iff (X Y : FDRep k G) [Simple X] [Simple Y] :
    mk X = mk Y ↔ Nonempty (X ≅ Y) :=
  ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso
    (Simple : ObjectProperty (FDRep k G)) _ _

/-- To prove a property of every simple-object class, it suffices to prove it on the class of each
simple object. -/
@[elab_as_elim]
theorem ind {motive : SimpleFDRepClasses k G → Prop}
    (h : ∀ (X : FDRep k G) (hX : Simple X), motive (@mk k G _ _ X hX))
    (c : SimpleFDRepClasses k G) :
    motive c :=
  Skeleton.ind (fun X ↦ h X.obj X.property) c

/-- Define a function on simple-object classes from an isomorphism-invariant function on simple
objects. -/
noncomputable def lift {α : Sort*} (f : ∀ (X : FDRep k G), Simple X → α)
    (h : ∀ (X Y : FDRep k G) (hX : Simple X) (hY : Simple Y),
      Nonempty (X ≅ Y) → f X hX = f Y hY) :
    SimpleFDRepClasses k G → α :=
  Skeleton.lift
    (fun X ↦ f X.obj X.property)
    fun X Y e ↦ h X.obj Y.obj X.property Y.property
      ⟨(ObjectProperty.ι (Simple : ObjectProperty (FDRep k G))).mapIso e.some⟩

@[simp]
theorem lift_mk {α : Sort*} (f : ∀ (X : FDRep k G), Simple X → α)
    (h : ∀ (X Y : FDRep k G) (hX : Simple X) (hY : Simple Y),
      Nonempty (X ≅ Y) → f X hX = f Y hY)
    (X : FDRep k G) [Simple X] : lift f h (mk X) = f X inferInstance := by
  simp [lift, mk]

end SimpleFDRepClasses

end Ring

namespace SimpleFDRepClasses

section Field

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- **The isomorphism class of the `k[G]`-module a simple object of `FDRep k G` carries.** Over a
semisimple group algebra this compares the categorical classification with the module-level one of
`TauCeti.SimpleSubmoduleClasses`. -/
noncomputable def toSimpleSubmoduleClasses [IsSemisimpleRing k[G]] :
    SimpleFDRepClasses k G → SimpleSubmoduleClasses k[G] k[G] :=
  lift
    (fun X hX ↦
      let _ := hX
      let _ : _root_.Representation.IsIrreducible X.ρ :=
        (FDRep.simple_iff_isIrreducible X).mp hX
      simpleModuleClass k[G] (_root_.Representation.asModule X.ρ))
    fun X Y hX hY h ↦ by
      let _ := hX
      let _ := hY
      let _ : _root_.Representation.IsIrreducible X.ρ :=
        (FDRep.simple_iff_isIrreducible X).mp hX
      let _ : _root_.Representation.IsIrreducible Y.ρ :=
        (FDRep.simple_iff_isIrreducible Y).mp hY
      exact simpleModuleClass_eq_iff.mpr
        (Representation.nonempty_equiv_iff.mp (nonempty_fdRepIso_iff.mp h))

@[simp]
theorem toSimpleSubmoduleClasses_mk [IsSemisimpleRing k[G]] (X : FDRep k G) [Simple X] :
    toSimpleSubmoduleClasses (mk X) =
      let _ : _root_.Representation.IsIrreducible X.ρ :=
        (FDRep.simple_iff_isIrreducible X).mp inferInstance
      simpleModuleClass k[G] (_root_.Representation.asModule X.ρ) :=
  lift_mk _ _ X

end Field

end SimpleFDRepClasses

end TauCeti
