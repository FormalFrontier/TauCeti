/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Descent
public import TauCeti.LinearAlgebra.BilinearMap.NumericalQuotient.Basic

/-!
# Numerical quotients of the Ext-Euler pairing

The Ext-Euler characteristic descends to a biadditive pairing on the exact Grothendieck groups of
two extension-closed subcategories. This file views that pairing as an integer-bilinear map and
applies the separate left and right numerical-quotient construction to it.

The two subcategories are deliberately kept independent: the Ext-Euler pairing is generally
nonsymmetric, so its left and right radicals can differ. The generic numerical-quotient API supplies
the quotient maps, one-sided pairings, functoriality, and the nondegenerate pairing; this file adds
the Ext-Euler names and the computation rules needed by its users.

## Main definitions

* `TauCeti.extEulerBilinear`: the integer-bilinear form underlying the descended Ext-Euler
  pairing.
* `TauCeti.ExtEulerLeftNumericalQuotient` and
  `TauCeti.ExtEulerRightNumericalQuotient`: the two numerical Grothendieck groups.
* `TauCeti.extEulerNumericalPairing`: the induced pairing between those two quotients.

## Main results

* `TauCeti.mem_extEulerLeftRadical_iff` and
  `TauCeti.mem_extEulerRightRadical_iff` characterize the two radicals using the Ext-Euler
  pairing.
* `TauCeti.extEulerNumericalPairing_mk` computes the quotient pairing on representatives.
* `TauCeti.extEulerNumericalPairing_unique` gives its universal characterization, and
  `TauCeti.extEulerNumericalPairing_nondegenerate` records the resulting two-sided
  nondegeneracy.

This is the ordinary Ext-Euler specialization in Layer 7 of the Grothendieck-groups,
Cartan-maps, and Euler-forms roadmap. The Laurent/sesquilinear specialization belongs after the
graded Ext-Euler pairing has descended to graded `K₀`.

## References

The Ext-Euler construction follows Weibel, *An Introduction to Homological Algebra*, Sections
2.4--2.7, and its nonsymmetric numerical quotient follows Dancso--Licata, *Koszul algebras and
flow lattices*, Section 3.1. No formalization is copied or vendored here; the two constructions
are combined through the existing Tau Ceti APIs.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] [LocallySmall.{w} C]

variable {P Q : ObjectProperty C}

section Definitions

variable [P.EssentiallySmall.{w}] [Q.EssentiallySmall.{w}]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

variable (hP : (ExactStructure.abelian C).IsExtensionClosed P)
  (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
  (h : IsEulerAdmissibleOn.{w} k P Q)

/-- The ordinary Ext-Euler pairing on exact Grothendieck groups, regarded as a bilinear map over
`ℤ` so that it can be fed to the numerical-quotient construction. -/
noncomputable def extEulerBilinear :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →ₗ[ℤ]
      ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →ₗ[ℤ] ℤ :=
  biadditiveToIntBilinear (extEulerPairing hP hQ h)

@[simp]
theorem extEulerBilinear_apply
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP))
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerBilinear hP hQ h x y = extEulerPairing hP hQ h x y :=
  biadditiveToIntBilinear_apply (extEulerPairing hP hQ h) x y

/-- The left numerical quotient of the first exact Grothendieck group for the Ext-Euler pairing. -/
abbrev ExtEulerLeftNumericalQuotient :=
  LeftNumericalQuotient (extEulerBilinear hP hQ h)

/-- The right numerical quotient of the second exact Grothendieck group for the Ext-Euler
pairing. -/
abbrev ExtEulerRightNumericalQuotient :=
  RightNumericalQuotient (extEulerBilinear hP hQ h)

/-- The quotient map from the first exact Grothendieck group to its Ext-Euler numerical quotient. -/
noncomputable def extEulerLeftNumericalQuotientMk :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →ₗ[ℤ]
      ExtEulerLeftNumericalQuotient hP hQ h :=
  leftNumericalQuotientMk (extEulerBilinear hP hQ h)

/-- The quotient map from the second exact Grothendieck group to its Ext-Euler numerical
quotient. -/
noncomputable def extEulerRightNumericalQuotientMk :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →ₗ[ℤ]
      ExtEulerRightNumericalQuotient hP hQ h :=
  rightNumericalQuotientMk (extEulerBilinear hP hQ h)

/-- The left radical of the Ext-Euler pairing, characterized by vanishing against every class on
the right. -/
theorem mem_extEulerLeftRadical_iff
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP)) :
    x ∈ leftRadical (extEulerBilinear hP hQ h) ↔
      ∀ y, extEulerPairing hP hQ h x y = 0 := by
  simp only [mem_leftRadical_iff, extEulerBilinear_apply]

/-- The right radical of the Ext-Euler pairing, characterized by vanishing against every class on
the left. -/
theorem mem_extEulerRightRadical_iff
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    y ∈ rightRadical (extEulerBilinear hP hQ h) ↔
      ∀ x, extEulerPairing hP hQ h x y = 0 := by
  simp only [mem_rightRadical_iff, extEulerBilinear_apply]

/-- The one-sided pairing after quotienting the left exact Grothendieck group. -/
noncomputable def extEulerLeftNumericalPairing :
    ExtEulerLeftNumericalQuotient hP hQ h →ₗ[ℤ]
      ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →ₗ[ℤ] ℤ :=
  leftNumericalPairing (extEulerBilinear hP hQ h)

/-- The one-sided pairing after quotienting the right exact Grothendieck group. -/
noncomputable def extEulerRightNumericalPairing :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →ₗ[ℤ]
      ExtEulerRightNumericalQuotient hP hQ h →ₗ[ℤ] ℤ :=
  rightNumericalPairing (extEulerBilinear hP hQ h)

/-- The Ext-Euler pairing between both numerical Grothendieck groups. -/
noncomputable def extEulerNumericalPairing :
    ExtEulerLeftNumericalQuotient hP hQ h →ₗ[ℤ]
      ExtEulerRightNumericalQuotient hP hQ h →ₗ[ℤ] ℤ :=
  numericalPairing (extEulerBilinear hP hQ h)

end Definitions

section Pairing

variable [P.EssentiallySmall.{w}] [Q.EssentiallySmall.{w}]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

variable (hP : (ExactStructure.abelian C).IsExtensionClosed P)
  (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
  (h : IsEulerAdmissibleOn.{w} k P Q)

/-- The left Ext-Euler numerical pairing evaluates on a quotient representative as the descended
Ext-Euler pairing. -/
@[simp]
theorem extEulerLeftNumericalPairing_mk
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP))
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerLeftNumericalPairing hP hQ h
        (extEulerLeftNumericalQuotientMk hP hQ h x) y =
      extEulerPairing hP hQ h x y := by
  rw [extEulerLeftNumericalPairing, extEulerLeftNumericalQuotientMk,
    leftNumericalPairing_mk, extEulerBilinear_apply]

/-- The right Ext-Euler numerical pairing evaluates on a quotient representative as the descended
Ext-Euler pairing. -/
@[simp]
theorem extEulerRightNumericalPairing_mk
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP))
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerRightNumericalPairing hP hQ h x
        (extEulerRightNumericalQuotientMk hP hQ h y) =
      extEulerPairing hP hQ h x y := by
  rw [extEulerRightNumericalPairing, extEulerRightNumericalQuotientMk,
    rightNumericalPairing_mk, extEulerBilinear_apply]

/-- The Ext-Euler numerical pairing evaluates on two quotient representatives as the descended
Ext-Euler pairing. -/
@[simp]
theorem extEulerNumericalPairing_mk (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP))
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerNumericalPairing hP hQ h
        (extEulerLeftNumericalQuotientMk hP hQ h x)
        (extEulerRightNumericalQuotientMk hP hQ h y) =
      extEulerPairing hP hQ h x y := by
  rw [extEulerNumericalPairing, extEulerLeftNumericalQuotientMk,
    extEulerRightNumericalQuotientMk, numericalPairing_mk, extEulerBilinear_apply]

/-- The Ext-Euler numerical pairing evaluates on classes of objects as the ordinary Ext-Euler
characteristic. -/
theorem extEulerNumericalPairing_of_of (X : P.FullSubcategory) (Y : Q.FullSubcategory) :
    extEulerNumericalPairing hP hQ h
        (extEulerLeftNumericalQuotientMk hP hQ h (ExactK0.of X))
        (extEulerRightNumericalQuotientMk hP hQ h (ExactK0.of Y)) =
      extEuler.{w} k (h.isEulerAdmissible X.property Y.property) := by
  rw [extEulerNumericalPairing_mk, extEulerPairing_of_of]

/-- The left numerical Ext-Euler pairing separates its left argument. -/
theorem extEulerLeftNumericalPairing_separatingLeft :
    (extEulerLeftNumericalPairing hP hQ h).SeparatingLeft :=
  leftNumericalPairing_separatingLeft (extEulerBilinear hP hQ h)

/-- The right numerical Ext-Euler pairing separates its right argument. -/
theorem extEulerRightNumericalPairing_separatingRight :
    (extEulerRightNumericalPairing hP hQ h).SeparatingRight :=
  rightNumericalPairing_separatingRight (extEulerBilinear hP hQ h)

/-- Quotienting by both Ext-Euler radicals makes the ordinary numerical pairing nondegenerate. -/
theorem extEulerNumericalPairing_nondegenerate :
    (extEulerNumericalPairing hP hQ h).Nondegenerate :=
  numericalPairing_nondegenerate (extEulerBilinear hP hQ h)

/-- The Ext-Euler numerical pairing is the unique bilinear pairing whose representative values are
the descended Ext-Euler values. -/
theorem extEulerNumericalPairing_unique
    (c : ExtEulerLeftNumericalQuotient hP hQ h →ₗ[ℤ]
      ExtEulerRightNumericalQuotient hP hQ h →ₗ[ℤ] ℤ)
    (hc : ∀ x y, c (extEulerLeftNumericalQuotientMk hP hQ h x)
        (extEulerRightNumericalQuotientMk hP hQ h y) = extEulerPairing hP hQ h x y) :
    c = extEulerNumericalPairing hP hQ h := by
  apply numericalPairing_unique (extEulerBilinear hP hQ h) c
  intro x y
  simpa only [extEulerLeftNumericalQuotientMk, extEulerRightNumericalQuotientMk,
    extEulerBilinear_apply] using hc x y

end Pairing

end TauCeti
