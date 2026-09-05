/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.Graded.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Graded exact structures on full subcategories

An extension-closed full subcategory of an exact category inherits an exact structure.  If the
ambient category is graded and the object property is invariant under the grading shift, that
shift restricts to an autoequivalence of the full subcategory and makes its induced exact
structure graded.

Invariance under the forward shift is enough: repleteness of the object property and the unit and
counit isomorphisms imply invariance under the inverse shift.  The restricted equivalence is
Mathlib's `CategoryTheory.Equivalence.congrFullSubcategory`; its functor and inverse preserve
conflations because the ambient shift and inverse shift do.

This construction is the bridge between objectwise graded invariants on extension-closed classes
and the Laurent-module Grothendieck groups of those classes.  In particular, it lets a graded
Ext-Euler characteristic descend to the graded Grothendieck groups of selected subcategories.

## Main definitions

* `TauCeti.GradedExactStructure.fullSubcategoryShift`: the grading-shift autoequivalence restricted
  to a shift-stable full subcategory.
* `TauCeti.GradedExactStructure.fullSubcategory`: the induced graded exact structure.

## Main results

* `TauCeti.GradedExactStructure.fullSubcategory_toExactStructure`: forgetting the grading recovers
  the induced exact structure.
* `TauCeti.GradedExactStructure.fullSubcategory_shift`: the shift of the induced structure is the
  restricted ambient shift.
* `TauCeti.GradedExactStructure.gradedConflationExactInclusion`: the inclusion is graded
  conflation-exact.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for grading shifts on exact
  categories and their graded Grothendieck groups.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

namespace GradedExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
variable (E : GradedExactStructure C) (P : ObjectProperty C)

section Shift

variable [P.IsClosedUnderIsomorphisms]

/-- The grading shift restricted to a full subcategory stable under that shift.

The equation `P.inverseImage E.shift.functor = P` states exactly that an object belongs to `P`
if and only if its shift does.  Mathlib's full-subcategory restriction of an equivalence then
uses the ambient inverse shift as its inverse. -/
abbrev fullSubcategoryShift (hshift : P.inverseImage E.shift.functor = P) :
    P.FullSubcategory ≌ P.FullSubcategory :=
  { E.shift.congrFullSubcategory hshift with
    functor := P.lift (P.ι ⋙ E.shift.functor) (fun X ↦ by
      have hX : P.inverseImage E.shift.functor X.obj := by
        rw [hshift]
        exact X.property
      exact hX)
    inverse := P.lift (P.ι ⋙ E.shift.inverse) (fun X ↦ by
      have hX : P.inverseImage E.shift.functor (E.shift.inverse.obj X.obj) :=
        P.prop_of_iso (E.shift.counitIso.app X.obj).symm X.property
      rw [hshift] at hX
      exact hX) }

/-- The inclusion of the full subcategory intertwines its restricted shift with the ambient
shift. -/
def fullSubcategoryShiftFunctorCompιIso
    (hshift : P.inverseImage E.shift.functor = P) :
    (fullSubcategoryShift E P hshift).functor ⋙ P.ι ≅ P.ι ⋙ E.shift.functor := by
  rw [fullSubcategoryShift]
  exact P.liftCompιIso (P.ι ⋙ E.shift.functor) (fun X => by
    have hX : P.inverseImage E.shift.functor X.obj := by
      rw [hshift]
      exact X.property
    exact hX)

/-- The inclusion of the full subcategory also intertwines the inverse restricted shift with the
ambient inverse shift. -/
def fullSubcategoryShiftInverseCompιIso
    (hshift : P.inverseImage E.shift.functor = P) :
    (fullSubcategoryShift E P hshift).inverse ⋙ P.ι ≅ P.ι ⋙ E.shift.inverse := by
  rw [fullSubcategoryShift]
  exact P.liftCompιIso (P.ι ⋙ E.shift.inverse) (fun X => by
    have hX : P.inverseImage E.shift.functor (E.shift.inverse.obj X.obj) :=
      P.prop_of_iso (E.shift.counitIso.app X.obj).symm X.property
    rw [hshift] at hX
    exact hX)

end Shift

section FullSubcategory

variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts]

local instance : P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

private theorem fullSubcategoryShift_exact
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    (E.toExactStructure.fullSubcategory P hP).IsConflationExact
      (E.toExactStructure.fullSubcategory P hP) (fullSubcategoryShift E P hshift).functor where
  map_conflation {S} hS := by
    rw [ExactStructure.fullSubcategory_conflation_iff] at hS ⊢
    exact E.shift_exact.map_conflation hS

private theorem fullSubcategoryShift_inverse_exact
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    (E.toExactStructure.fullSubcategory P hP).IsConflationExact
      (E.toExactStructure.fullSubcategory P hP) (fullSubcategoryShift E P hshift).inverse where
  map_conflation {S} hS := by
    rw [ExactStructure.fullSubcategory_conflation_iff] at hS ⊢
    exact E.shift_inverse_exact.map_conflation hS

/-- The graded exact structure induced on a shift-stable, extension-closed full subcategory.

Its exact structure is the one induced from the ambient exact category, and its grading shift is
the restriction of the ambient shift. -/
noncomputable def fullSubcategory
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    GradedExactStructure P.FullSubcategory where
  toExactStructure := E.toExactStructure.fullSubcategory P hP
  shift := fullSubcategoryShift E P hshift
  shift_exact := fullSubcategoryShift_exact E P hP hshift
  shift_inverse_exact := fullSubcategoryShift_inverse_exact E P hP hshift

@[simp]
theorem fullSubcategory_toExactStructure
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    (fullSubcategory E P hP hshift).toExactStructure =
      E.toExactStructure.fullSubcategory P hP :=
  by rw [fullSubcategory]

@[simp]
theorem fullSubcategory_shift
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    (fullSubcategory E P hP hshift).shift = fullSubcategoryShift E P hshift :=
  by rw [fullSubcategory]

/-- The inclusion of a shift-stable, extension-closed full subcategory is graded
conflation-exact.  Its commutation isomorphism is the canonical comparison between the restricted
shift followed by inclusion and the ambient shift. -/
def gradedConflationExactInclusion
    (hP : E.toExactStructure.IsExtensionClosed P)
    (hshift : P.inverseImage E.shift.functor = P) :
    GradedConflationExact (fullSubcategory E P hP hshift) E P.ι where
  isConflationExact := ExactStructure.isConflationExact_ι hP
  commShift := fullSubcategoryShiftFunctorCompιIso E P hshift

end FullSubcategory

end GradedExactStructure

end TauCeti
