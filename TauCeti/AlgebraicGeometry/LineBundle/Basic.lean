/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Invertible sheaves on a scheme

This file begins the scheme-level line-bundle lane of the Jacobian challenge. An invertible
sheaf on a scheme `X` is an `𝒪_X`-module which is locally free of rank one.

The rank-one condition itself is not specific to schemes: it is
`TauCeti.SheafOfModules.IsInvertible` from
`TauCeti/Algebra/Category/ModuleCat/Sheaf/Invertible/Basic.lean`, stated for a sheaf of modules
over an arbitrary site. This file only packages it over a scheme:

* `TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X` is the `ObjectProperty` on `X.Modules`
  cut out by the predicate (closed under isomorphisms, by the site-level transport theorem, so
  `ObjectProperty.prop_of_iso` and `ObjectProperty.prop_iff_of_iso` apply to it);
* `TauCeti.AlgebraicGeometry.InvertibleSheaf X` is the full subcategory it cuts out;
* `InvertibleSheaf.free X I` is the free sheaf on an indexing type with exactly one element, and
  `InvertibleSheaf.trivial X` is the globally free rank-one sheaf.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a
scheme; the Picard group `Pic X` under `⊗`". The tensor product and Picard group require a
monoidal structure on sheaves of modules and are left to subsequent files. No formalization is
vendored.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SheafOfModules

variable (X : Scheme.{u})

/-- The object property of being an invertible sheaf on a scheme. -/
abbrev isInvertible : ObjectProperty X.Modules :=
  TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf)

instance : (isInvertible X).IsClosedUnderIsomorphisms where
  of_iso e hM := by
    haveI := hM
    exact TauCeti.SheafOfModules.IsInvertible.of_iso (R := X.ringCatSheaf) e

end SheafOfModules

variable {X : Scheme.{u}}

/-- The full category of invertible sheaves on `X`. Its morphisms are morphisms of
`𝒪_X`-modules. -/
abbrev InvertibleSheaf (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (SheafOfModules.isInvertible X)

namespace InvertibleSheaf

instance (L : InvertibleSheaf X) : SheafOfModules.isInvertible X L.obj :=
  L.property

/-- The invertible sheaf given by the free sheaf on an indexing type with exactly one element. -/
def free (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    InvertibleSheaf X :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) I, inferInstance⟩

@[simp]
lemma free_obj (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    (free X I).obj = SheafOfModules.free (R := X.ringCatSheaf) I :=
  (rfl)

/-- The globally free rank-one invertible sheaf. -/
def trivial (X : Scheme.{u}) : InvertibleSheaf X :=
  free X PUnit

@[simp]
lemma trivial_obj (X : Scheme.{u}) :
    (trivial X).obj = SheafOfModules.free (R := X.ringCatSheaf) PUnit :=
  (rfl)

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
