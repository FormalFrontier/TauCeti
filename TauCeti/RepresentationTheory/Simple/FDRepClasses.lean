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
`CategoryTheory.Skeleton`, whose underlying type is `Quotient (isIsomorphicSetoid _)` and whose
`CategoryTheory.toSkeleton` and `CategoryTheory.toSkeleton_eq_toSkeleton_iff` are the constructor
and the comparison. `TauCeti.SimpleFDRepClasses` is that skeleton, taken of the full subcategory of
simple objects, so all of Mathlib's skeleton API applies to it unchanged.

`TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses` compares it with the module-level quotient
over a semisimple group algebra, sending a simple object to the isomorphism class of the
`k[G]`-module it carries. It is what makes a categorical classification and a module-level
classification of the same group two readings of one bijection rather than two unrelated
bijections; see `TauCeti.coe_simpleFDRepClassesEquivSimpleModuleClasses` for the symmetric group.

## Main results

* `TauCeti.SimpleFDRepClasses`: the isomorphism classes of simple objects of `FDRep k G`.
* `TauCeti.toSkeleton_eq_toSkeleton_iff_nonempty_iso`: two simple objects have the same class
  exactly when they are isomorphic in `FDRep k G`, rather than merely in the full subcategory.
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

/-- Being simple, as a property of the objects of `FDRep k G`. -/
abbrev simpleObjects : ObjectProperty (FDRep k G) := fun X => Simple X

/-- **The isomorphism classes of simple objects of `FDRep k G`**: the skeleton of the full
subcategory they span. Build a class with `CategoryTheory.toSkeleton`, compare two with
`TauCeti.toSkeleton_eq_toSkeleton_iff_nonempty_iso`, and eliminate with `Quotient.ind` or
`Quotient.lift`, the skeleton being the quotient of the objects by isomorphism. -/
abbrev SimpleFDRepClasses : Type _ := Skeleton (simpleObjects k G).FullSubcategory

variable {k G}

/-- **Two simple objects have the same class exactly when they are isomorphic.** This is
`CategoryTheory.toSkeleton_eq_toSkeleton_iff` with the isomorphisms of the full subcategory of
simple objects traded for isomorphisms of `FDRep k G`, which is what a consumer holds. -/
theorem toSkeleton_eq_toSkeleton_iff_nonempty_iso {X Y : FDRep k G} (hX : Simple X)
    (hY : Simple Y) :
    toSkeleton (⟨X, hX⟩ : (simpleObjects k G).FullSubcategory) = toSkeleton ⟨Y, hY⟩ ↔
      Nonempty (X ≅ Y) := by
  rw [toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun ⟨e⟩ => ⟨(simpleObjects k G).ι.mapIso e⟩, fun ⟨e⟩ => ⟨ObjectProperty.isoMk _ e⟩⟩

namespace SimpleFDRepClasses

/-- **The isomorphism class of the `k[G]`-module a simple object of `FDRep k G` carries.** Over a
semisimple group algebra this compares the categorical classification with the module-level one of
`TauCeti.SimpleSubmoduleClasses`. -/
noncomputable def toSimpleSubmoduleClasses [IsSemisimpleRing k[G]] :
    SimpleFDRepClasses k G → SimpleSubmoduleClasses k[G] k[G] :=
  Quotient.lift
    (fun X =>
      letI := X.property
      simpleModuleClass k[G] (_root_.Representation.asModule X.obj.ρ))
    fun X Y h => by
      have := X.property
      have := Y.property
      exact simpleModuleClass_eq_iff.mpr (Representation.nonempty_equiv_iff.mp
        (nonempty_fdRepIso_iff.mp ⟨(simpleObjects k G).ι.mapIso h.some⟩))

@[simp]
theorem toSimpleSubmoduleClasses_toSkeleton [IsSemisimpleRing k[G]] (X : FDRep k G)
    (hX : Simple X) :
    toSimpleSubmoduleClasses (toSkeleton (⟨X, hX⟩ : (simpleObjects k G).FullSubcategory)) =
      letI := hX
      simpleModuleClass k[G] (_root_.Representation.asModule X.ρ) :=
  (rfl)

end SimpleFDRepClasses

end TauCeti
