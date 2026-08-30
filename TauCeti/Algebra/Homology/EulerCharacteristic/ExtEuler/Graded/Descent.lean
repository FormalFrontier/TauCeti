/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Additivity
public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian

/-!
# Descent of the graded Ext-Euler characteristic to K₀

For extension-closed object properties `P` and `Q`, pointwise graded Euler-admissibility makes the
Laurent-polynomial-valued Ext-Euler characteristic additive on every conflation in either
subcategory.  The universal property of exact `K₀` therefore gives a biadditive pairing between
their Grothendieck groups.

The two groups remain distinct because the pairing need not be symmetric.  This file records only
biadditivity.  The action of the grading shift and the resulting sesquilinear structure belong to
the q-Euler layer built on top of this pairing.

## Main definitions

* `TauCeti.IsGradedEulerAdmissibleOn`: every pair in two object properties is graded
  Euler-admissible.
* `TauCeti.gradedExtEulerPairing`: the graded Ext-Euler characteristic descended to exact `K₀` in
  both variables.

## Main results

* `TauCeti.gradedExtEulerPairing_of_of`: evaluation on two object classes.
* `TauCeti.gradedExtEulerPairing_unique`: the universal characterization of the pairing.

## References

* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 5, "Graded Ext and graded descent".
-/

public section

namespace TauCeti

open CategoryTheory

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] {e : C ≌ C}

/-- Every pair of objects in `P × Q` is graded Euler-admissible.  The internal-support and
cohomological bounds may depend on the pair. -/
structure IsGradedEulerAdmissibleOn (P Q : ObjectProperty C) : Prop where
  /-- Each pair drawn from `P` and `Q` is graded Euler-admissible. -/
  isGradedEulerAdmissible ⦃X Y : C⦄ (hX : P X) (hY : Q Y) :
    IsGradedEulerAdmissible.{w} k e X Y

/-- Graded Euler-admissibility on two object properties restricts to smaller properties. -/
theorem IsGradedEulerAdmissibleOn.mono {P P' Q Q' : ObjectProperty C}
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    (hP : P' ≤ P) (hQ : Q' ≤ Q) :
    IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P' Q' :=
  ⟨fun _ _ hX hY ↦ h.isGradedEulerAdmissible (hP _ hX) (hQ _ hY)⟩

variable {P Q : ObjectProperty C} [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

private noncomputable def gradedExtEulerRightInvariant
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) (X : P.FullSubcategory) :
    ExactK0.AdditiveInvariant ((ExactStructure.abelian C).fullSubcategory Q hQ)
      (LaurentPolynomial ℤ) where
  obj Y := gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property)
  map_iso {Y Y'} i :=
    gradedExtEuler_of_iso k
      (h.isGradedEulerAdmissible X.property Y.property)
      (h.isGradedEulerAdmissible X.property Y'.property) (Iso.refl X.obj) (Q.ι.mapIso i)
  map_conflation {S} hS := by
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
  ExactK0.lift (gradedExtEulerRightInvariant hQ h X)

omit [ObjectProperty.EssentiallySmall.{w} P] [P.ContainsZero]
  [P.IsClosedUnderBinaryProducts] in
@[simp]
theorem gradedExtEulerRight_of
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) (X : P.FullSubcategory)
    (Y : Q.FullSubcategory) :
    gradedExtEulerRight hQ h X (ExactK0.of Y) =
      gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property) :=
  ExactK0.lift_of _ Y

omit [ObjectProperty.EssentiallySmall.{w} P] [P.ContainsZero]
  [P.IsClosedUnderBinaryProducts] in
private theorem gradedExtEulerRight_congr
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    {X X' : P.FullSubcategory} (i : X ≅ X') :
    gradedExtEulerRight hQ h X = gradedExtEulerRight hQ h X' := by
  refine ExactK0.hom_ext fun Y ↦ ?_
  rw [gradedExtEulerRight_of, gradedExtEulerRight_of]
  exact gradedExtEuler_of_iso k
    (h.isGradedEulerAdmissible X.property Y.property)
    (h.isGradedEulerAdmissible X'.property Y.property) (P.ι.mapIso i) (Iso.refl Y.obj)

omit [ObjectProperty.EssentiallySmall.{w} P] in
private theorem gradedExtEulerRight_conflation
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    {S : ShortComplex P.FullSubcategory}
    (hS : ((ExactStructure.abelian C).fullSubcategory P hP).Conflation S) :
    gradedExtEulerRight hQ h S.X₂ =
      gradedExtEulerRight hQ h S.X₁ + gradedExtEulerRight hQ h S.X₃ := by
  refine ExactK0.hom_ext fun Y ↦ ?_
  simp only [gradedExtEulerRight_of, AddMonoidHom.add_apply]
  have hc : (ExactStructure.abelian C).Conflation (S.map P.ι) :=
    (ExactStructure.fullSubcategory_conflation_iff hP S).mp hS
  have hS' : (S.map P.ι).ShortExact := (ExactStructure.abelian_conflation _).mp hc
  exact gradedExtEuler_shortExact₁ hS' Y.obj
    (h.isGradedEulerAdmissible S.X₁.property Y.property)
    (h.isGradedEulerAdmissible S.X₃.property Y.property)

private noncomputable def gradedExtEulerLeftInvariant
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) :
    ExactK0.AdditiveInvariant ((ExactStructure.abelian C).fullSubcategory P hP)
      (ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →+ LaurentPolynomial ℤ) where
  obj := gradedExtEulerRight hQ h
  map_iso := fun {_ _} i ↦ gradedExtEulerRight_congr (P := P) (Q := Q) hQ h i
  map_conflation := fun {_} hS ↦
    gradedExtEulerRight_conflation (P := P) (Q := Q) hP hQ h hS

/-- The Laurent-polynomial-valued Ext-Euler pairing on the exact Grothendieck groups of two
extension-closed subcategories.  It is additive in both variables and is not asserted to be
symmetric. -/
noncomputable def gradedExtEulerPairing
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q) :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →+
      ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →+ LaurentPolynomial ℤ :=
  ExactK0.lift (gradedExtEulerLeftInvariant hP hQ h)

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
  rw [gradedExtEulerPairing, ExactK0.lift_of, gradedExtEulerLeftInvariant,
    gradedExtEulerRight_of]

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
  refine ExactK0.hom_ext fun X ↦ ExactK0.hom_ext fun Y ↦ ?_
  rw [hb, gradedExtEulerPairing_of_of]

end TauCeti
