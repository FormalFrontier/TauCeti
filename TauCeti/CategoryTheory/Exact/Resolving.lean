/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.Resolution

/-!
# Resolving subcategories of an exact category

Let `E` be an exact structure on an additive category `C`. A full subcategory `P` is **resolving**
when it is replete and additive, is closed under extensions, is closed under kernels of the
deflations between its objects, and every object of `C` admits a finite `P`-resolution. The
kernel condition is stated using the kernel--cokernel pairs carried by `E`, so this definition
does not assume that `C` has arbitrary kernels or cokernels.

The package in this file is the general-resolution prerequisite in Layer 3 of the
Grothendieck--Euler roadmap. It is deliberately separate from the projective-resolution package:
projectivity implies the extension and kernel closure needed for projective resolutions by the
horseshoe lemma, whereas a general resolving subcategory takes those closure properties as its
own hypotheses.

## Main definitions

* `TauCeti.ExactStructure.IsClosedUnderKernelsOfDeflations`: closure of an object property under
  the kernels in `E`-conflations whose middle and quotient lie in the property.
* `TauCeti.ExactStructure.IsResolving`: the complete resolving-subcategory package.
* `TauCeti.ExactStructure.IsResolving.inducedExactStructure`: the exact structure induced on the
  full subcategory of resolving objects.

## Main results

* `TauCeti.ExactStructure.IsResolving.prop_of_kernel_of_deflation`: the kernel-closure operation
  exposed in a form using the two maps of a conflation.
* `TauCeti.ExactStructure.IsResolving.isConflationExact_ι` and
  `TauCeti.ExactStructure.IsResolving.reflectsConflations_ι`: the full-subcategory inclusion
  preserves and reflects the induced conflations.

The finite-resolution field is the coverage hypothesis consumed by the general resolution theorem;
the theorem itself and its Euler-class comparison are downstream of this package.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 7,
  for resolving subcategories and the resolution theorem.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), Sections 11--12, for
  the exact-category resolution vocabulary and the distinction between projective and general
  resolving hypotheses.
* [The Tau Ceti Grothendieck groups, Cartan maps, and Euler forms roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/GrothendieckEulerForms/README.md),
  Layer 3, "Resolving subcategories".
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C) (P : ObjectProperty C)

/-- An object property is closed under kernels of admissible epimorphisms between its objects.

More precisely, if `S` is an `E`-conflation and both its middle object `S.X₂` and quotient
`S.X₃` satisfy `P`, then its kernel object `S.X₁` satisfies `P`. The first map of `S` is the
kernel and the second map is an `E`-deflation by the kernel--cokernel pair carried by `S`. -/
structure IsClosedUnderKernelsOfDeflations : Prop where
  /-- The kernel of a conflation between `P`-objects again satisfies `P`. -/
  prop_X₁ {S : ShortComplex C} (hS : E.Conflation S) (h₂ : P S.X₂) (h₃ : P S.X₃) : P S.X₁

namespace IsClosedUnderKernelsOfDeflations

variable {E P}

/-- The kernel-closure condition, with the conflation written by its two maps. -/
theorem prop_of_kernel_of_deflation {K Q X : C} {i : K ⟶ Q} {p : Q ⟶ X}
    {zero : i ≫ p = 0} (hS : E.Conflation (ShortComplex.mk i p zero)) (hQ : P Q) (hX : P X)
    (hP : E.IsClosedUnderKernelsOfDeflations P) : P K :=
  hP.prop_X₁ hS hQ hX

end IsClosedUnderKernelsOfDeflations

/-- A **resolving subcategory** of an exact category.

The first three parent classes say that `P` is replete and additive. The remaining fields are,
respectively, extension closure, closure under kernels of admissible epimorphisms between objects
of `P`, and existence of a finite `P`-resolution for every ambient object. -/
class IsResolving : Prop extends P.IsClosedUnderIsomorphisms, P.ContainsZero,
    P.IsClosedUnderBinaryProducts where
  /-- `P` is closed under extensions in `E`. -/
  isExtensionClosed : E.IsExtensionClosed P
  /-- `P` is closed under kernels of `E`-deflations between objects of `P`. -/
  isClosedUnderKernelsOfDeflations : E.IsClosedUnderKernelsOfDeflations P
  /-- Every object of `C` admits a finite resolution by objects of `P`. -/
  admitsFiniteResolution : ∀ X : C, E.admitsFiniteResolution P X

namespace IsResolving

variable {E P}

/-- The kernel-closure operation of a resolving subcategory. -/
theorem prop_of_kernel_of_deflation [hP : E.IsResolving P] {K Q X : C}
    {i : K ⟶ Q} {p : Q ⟶ X} {zero : i ≫ p = 0}
    (hS : E.Conflation (ShortComplex.mk i p zero)) (hQ : P Q) (hX : P X) : P K :=
  hP.isClosedUnderKernelsOfDeflations.prop_of_kernel_of_deflation hS hQ hX

/-- The exact structure induced on the full subcategory of resolving objects.

Its conflations are precisely the ambient `E`-conflations whose three terms satisfy `P`; the
existence and exactness of this structure use the extension-closure field of `hP`. -/
noncomputable def inducedExactStructure [hP : E.IsResolving P] :
    ExactStructure P.FullSubcategory :=
  E.fullSubcategory P hP.isExtensionClosed

@[simp]
theorem inducedExactStructure_conflation_iff [hP : E.IsResolving P]
    (S : ShortComplex P.FullSubcategory) :
    hP.inducedExactStructure.Conflation S ↔ E.Conflation (S.map P.ι) :=
  E.fullSubcategory_conflation_iff hP.isExtensionClosed S

/-- The inclusion of a resolving subcategory is conflation-exact. -/
theorem isConflationExact_ι [hP : E.IsResolving P] :
    hP.inducedExactStructure.IsConflationExact E P.ι :=
  E.isConflationExact_ι hP.isExtensionClosed

/-- The inclusion of a resolving subcategory reflects conflations. -/
theorem reflectsConflations_ι [hP : E.IsResolving P] :
    hP.inducedExactStructure.ReflectsConflations E P.ι :=
  E.reflectsConflations_ι hP.isExtensionClosed

end IsResolving

end ExactStructure

end TauCeti
