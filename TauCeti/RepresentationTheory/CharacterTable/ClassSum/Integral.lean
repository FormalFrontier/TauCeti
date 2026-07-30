/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Integrality of class sums

For a finite group `G`, the class sums form a finite basis of the center of the integral
group algebra `ℤ[G]`. Consequently every element of this center, and in particular every
class sum, is integral over `ℤ`.

The point is to establish integrality inside `Z(ℤ[G])`. Integrality of a class sum merely as
an element of `ℤ[G]` would not retain the central algebra through which central characters
factor.

## References

* [Character Theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 1, “The integral class center”.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory*, Volume I, Chapters 1–3.
-/

public section

namespace TauCeti

/-- The center of `ℤ[G]` is finite as a `ℤ`-module, with its class-sum basis. -/
noncomputable instance instModuleFiniteCenterIntMonoidAlgebra
    {G : Type*} [Group G] [Finite G] :
    Module.Finite ℤ (Subalgebra.center ℤ (MonoidAlgebra ℤ G)) :=
  by
    letI := Fintype.ofFinite G
    letI := Classical.decEq G
    exact Module.Finite.of_basis classSumBasis

/-- A class sum is integral over `ℤ` as an element of the center of `ℤ[G]`. -/
theorem isIntegral_classSum {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (C : ConjClasses G) :
    IsIntegral ℤ
      (⟨classSum ℤ C, classSum_mem_center ℤ C⟩ :
        Subalgebra.center ℤ (MonoidAlgebra ℤ G)) :=
  Algebra.IsIntegral.isIntegral _

end TauCeti
