/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Skeletal
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

namespace TauCeti

open scoped MonoidAlgebra

universe u v

variable (k : Type u) (G : Type v) [Field k] [Monoid G]

namespace ObjectProperty

/-- Two objects of a full subcategory define the same point of its skeleton exactly when the
underlying objects are isomorphic. -/
theorem toSkeleton_eq_toSkeleton_iff_nonempty_iso {C : Type*} [Category C]
    (P : CategoryTheory.ObjectProperty C) {X Y : C} (hX : P X) (hY : P Y) :
    toSkeleton (⟨X, hX⟩ : P.FullSubcategory) = toSkeleton ⟨Y, hY⟩ ↔ Nonempty (X ≅ Y) := by
  rw [CategoryTheory.toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨P.ι.mapIso e⟩, fun ⟨e⟩ ↦ ⟨CategoryTheory.ObjectProperty.isoMk _ e⟩⟩

end ObjectProperty

namespace FDRep

/-- Being simple, as a property of the objects of `FDRep k G`. -/
abbrev simpleObjects : ObjectProperty (FDRep k G) := fun X => Simple X

instance : (simpleObjects k G).IsClosedUnderIsomorphisms where
  of_iso e h := by
    let _ := h
    exact Simple.of_iso e.symm

end FDRep

/-- **The isomorphism classes of simple objects of `FDRep k G`**: the skeleton of the full
subcategory they span. -/
abbrev SimpleFDRepClasses : Type _ := Skeleton (FDRep.simpleObjects k G).FullSubcategory

variable {k G}

namespace SimpleFDRepClasses

/-- The isomorphism class of a simple object of `FDRep k G`. -/
def mk (X : FDRep k G) [Simple X] : SimpleFDRepClasses k G :=
  toSkeleton (⟨X, inferInstance⟩ : (FDRep.simpleObjects k G).FullSubcategory)

/-- Two simple objects have the same class exactly when they are isomorphic. -/
@[simp]
theorem mk_eq_mk_iff (X Y : FDRep k G) [Simple X] [Simple Y] :
    mk X = mk Y ↔ Nonempty (X ≅ Y) :=
  ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso (FDRep.simpleObjects k G) _ _

/-- To prove a property of every simple-object class, it suffices to prove it on the class of each
simple object. -/
@[elab_as_elim]
theorem ind {motive : SimpleFDRepClasses k G → Prop}
    (h : ∀ (X : FDRep k G) (hX : Simple X), motive (@mk k G _ _ X hX))
    (c : SimpleFDRepClasses k G) :
    motive c := by
  refine Quotient.ind (fun X ↦ ?_) c
  exact h X.obj X.property

/-- Define a function on simple-object classes from an isomorphism-invariant function on simple
objects. -/
noncomputable def lift {α : Sort*} (f : ∀ (X : FDRep k G), Simple X → α)
    (h : ∀ (X Y : FDRep k G) (hX : Simple X) (hY : Simple Y),
      Nonempty (X ≅ Y) → f X hX = f Y hY) :
    SimpleFDRepClasses k G → α :=
  Quotient.lift
    (fun X ↦ f X.obj X.property)
    fun X Y e ↦ h X.obj Y.obj X.property Y.property
      ⟨(FDRep.simpleObjects k G).ι.mapIso e.some⟩

@[simp]
theorem lift_mk {α : Sort*} (f : ∀ (X : FDRep k G), Simple X → α)
    (h : ∀ (X Y : FDRep k G) (hX : Simple X) (hY : Simple Y),
      Nonempty (X ≅ Y) → f X hX = f Y hY)
    (X : FDRep k G) [Simple X] : lift f h (mk X) = f X inferInstance := by
  simp [lift, mk]

/-- **The isomorphism class of the `k[G]`-module a simple object of `FDRep k G` carries.** Over a
semisimple group algebra this compares the categorical classification with the module-level one of
`TauCeti.SimpleSubmoduleClasses`. -/
noncomputable def toSimpleSubmoduleClasses [IsSemisimpleRing k[G]] :
    SimpleFDRepClasses k G → SimpleSubmoduleClasses k[G] k[G] :=
  lift
    (fun X hX ↦
      let _ := hX
      simpleModuleClass k[G] (_root_.Representation.asModule X.ρ))
    fun X Y hX hY h ↦ by
      let _ := hX
      let _ := hY
      exact simpleModuleClass_eq_iff.mpr
        (Representation.nonempty_equiv_iff.mp (nonempty_fdRepIso_iff.mp h))

@[simp]
theorem toSimpleSubmoduleClasses_mk [IsSemisimpleRing k[G]] (X : FDRep k G) [Simple X] :
    toSimpleSubmoduleClasses (mk X) =
      simpleModuleClass k[G] (_root_.Representation.asModule X.ρ) :=
  lift_mk _ _ X

end SimpleFDRepClasses

end TauCeti
