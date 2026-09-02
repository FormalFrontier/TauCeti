/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Additivity

/-!
# Preliminary exact-K₀ descent of the graded Ext-Euler characteristic

For extension-closed object properties `P` and `Q`, pointwise graded Euler-admissibility makes the
Laurent-polynomial-valued Ext-Euler characteristic additive on every conflation in either
subcategory.  The universal property of exact `K₀` therefore gives a biadditive pairing between
their Grothendieck groups.

The two groups remain distinct because the pairing need not be symmetric.  This file records only
biadditivity on ordinary exact `K₀`.  Descent to graded `K₀` additionally requires shift identities
and shift-closed subcategories; those belong to the later sesquilinear packaging of this preliminary
pairing.

## Main definitions

* `TauCeti.gradedExtEulerRight`: the graded Ext-Euler characteristic with its first argument
  fixed, descended to exact `K₀` in the second variable.
* `TauCeti.gradedExtEulerPairing`: the graded Ext-Euler characteristic descended to exact `K₀` in
  both variables.

## Main results

* `TauCeti.gradedExtEulerPairing_of_of`: evaluation on two object classes.
* `TauCeti.gradedExtEulerPairing_unique`: the universal characterization of the pairing.

## References

* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 6, "q-Euler form".
-/

public section

namespace TauCeti

open CategoryTheory

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] {e : C ≌ C}

variable {P Q : ObjectProperty C} [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

private noncomputable def gradedExtEulerRightAdditiveInvariant
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) :
    ExactK0.RightAdditiveInvariant P.FullSubcategory
      ((ExactStructure.abelian C).fullSubcategory Q hQ) (LaurentPolynomial ℤ) where
  obj X Y := gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property)
  map_iso₁ {X X'} i Y :=
    gradedExtEuler_of_iso k
      (h.isGradedEulerAdmissible X.property Y.property)
      (h.isGradedEulerAdmissible X'.property Y.property) (P.ι.mapIso i) (Iso.refl Y.obj)
  map_iso₂ X {Y Y'} i :=
    gradedExtEuler_of_iso k
      (h.isGradedEulerAdmissible X.property Y.property)
      (h.isGradedEulerAdmissible X.property Y'.property) (Iso.refl X.obj) (Q.ι.mapIso i)
  map_conflation₂ X {S} hS := by
    have hc : (ExactStructure.abelian C).Conflation (S.map Q.ι) :=
      (ExactStructure.fullSubcategory_conflation_iff hQ S).mp hS
    have hS' : (S.map Q.ι).ShortExact := (ExactStructure.abelian_conflation _).mp hc
    exact gradedExtEuler_shortExact₂ hS' X.obj
      (h.isGradedEulerAdmissible X.property S.X₁.property)
      (h.isGradedEulerAdmissible X.property S.X₃.property)

/-- For a fixed object in `P`, the graded Ext-Euler characteristic descends in the second
variable to the exact `K₀` of the extension-closed subcategory on `Q`. -/
noncomputable def gradedExtEulerRight
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) (X : P.FullSubcategory) :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →+ LaurentPolynomial ℤ :=
  (gradedExtEulerRightAdditiveInvariant hQ h).rightLift X

omit [ObjectProperty.EssentiallySmall.{w} P] [P.ContainsZero]
  [P.IsClosedUnderBinaryProducts] in
/-- `gradedExtEulerRight` evaluates on an object class as the object-level graded Ext-Euler
characteristic. -/
@[simp]
theorem gradedExtEulerRight_of
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) (X : P.FullSubcategory)
    (Y : Q.FullSubcategory) :
    gradedExtEulerRight hQ h X (ExactK0.of Y) =
      gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property) :=
  ExactK0.RightAdditiveInvariant.rightLift_of _ X Y

private noncomputable def gradedExtEulerBiadditiveInvariant
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) :
    ExactK0.BiadditiveInvariant ((ExactStructure.abelian C).fullSubcategory P hP)
      ((ExactStructure.abelian C).fullSubcategory Q hQ) (LaurentPolynomial ℤ) where
  toRightAdditiveInvariant := gradedExtEulerRightAdditiveInvariant hQ h
  map_conflation₁ {S} hS Y := by
    have hc : (ExactStructure.abelian C).Conflation (S.map P.ι) :=
      (ExactStructure.fullSubcategory_conflation_iff hP S).mp hS
    have hS' : (S.map P.ι).ShortExact := (ExactStructure.abelian_conflation _).mp hc
    exact gradedExtEuler_shortExact₁ hS' Y.obj
      (h.isGradedEulerAdmissible S.X₁.property Y.property)
      (h.isGradedEulerAdmissible S.X₃.property Y.property)

/-- The Laurent-polynomial-valued Ext-Euler pairing on the exact Grothendieck groups of two
extension-closed subcategories.  It is additive in both variables and is not asserted to be
symmetric. -/
noncomputable def gradedExtEulerPairing
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →+
      ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →+ LaurentPolynomial ℤ :=
  (gradedExtEulerBiadditiveInvariant hP hQ h).bilift

/-- The descended graded Ext-Euler pairing evaluates on object classes as the original
object-level characteristic. -/
@[simp]
theorem gradedExtEulerPairing_of_of
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) (X : P.FullSubcategory)
    (Y : Q.FullSubcategory) :
    gradedExtEulerPairing hP hQ h (ExactK0.of X) (ExactK0.of Y) =
      gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property) := by
  exact ExactK0.BiadditiveInvariant.bilift_of_of _ X Y

/-- The descended pairing is the unique biadditive map with the prescribed values on pairs of
object classes. -/
theorem gradedExtEulerPairing_unique
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    (b : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →+
      ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →+ LaurentPolynomial ℤ)
    (hb : ∀ (X : P.FullSubcategory) (Y : Q.FullSubcategory),
      b (ExactK0.of X) (ExactK0.of Y) =
        gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property)) :
    b = gradedExtEulerPairing hP hQ h := by
  exact ExactK0.BiadditiveInvariant.bilift_unique _ b hb

end TauCeti
