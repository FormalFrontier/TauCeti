/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

The same statement over an arbitrary coefficient ring `k` follows by base change along
`ℤ[G] → k[G]`, which carries class sums to class sums; it cannot be proved by the argument over
`ℤ`, because `Z(k[G])` need not be a finite `ℤ`-module. This coefficient-general form is the one a
central character `Z(k[G]) →ₐ[k] k` can be applied to, so it is what makes the values of a central
character on the class sums algebraic integers.

## Main results

* `TauCeti.isIntegral_classSum`: a class sum is integral over `ℤ` in `Z(ℤ[G])`.
* `TauCeti.isIntegral_classSumCenter`: its base change, integrality over `ℤ` in `Z(k[G])` for an
  arbitrary commutative coefficient ring `k`.

## References

* [Character Theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 1, “The integral class center”.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory*, Volume I, Chapters 1–3.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- A class sum is integral over `ℤ` as an element of the center of `ℤ[G]`. -/
theorem isIntegral_classSum (C : ConjClasses G) :
    IsIntegral ℤ (classSumCenter (k := ℤ) C) :=
  Algebra.IsIntegral.isIntegral _

/-- A class sum is integral over `ℤ` as an element of the center of `k[G]`, for any coefficient
ring `k`.

The center of `k[G]` is not a finite `ℤ`-module, so this does not follow by the argument over `ℤ`;
it is transported from there along the base change `ℤ[G] → k[G]`, which carries class sums to class
sums. It is the input to the integrality of the values of a central character on the class
sums. -/
theorem isIntegral_classSumCenter (k : Type*) [CommRing k] (C : ConjClasses G) :
    IsIntegral ℤ (classSumCenter (k := k) C) := by
  -- integrality over `ℤ`, read in `ℤ[G]` rather than in its center
  have hZ : IsIntegral ℤ (classSum ℤ C) := by
    simpa using (isIntegral_classSum C).map (Subalgebra.center ℤ (MonoidAlgebra ℤ G)).val
  -- base change along the unique ring homomorphism `ℤ → k`, which fixes the class sums
  have hmap : MonoidAlgebra.mapAlgHom G (Algebra.ofId ℤ k) (classSum ℤ C) = classSum k C := by
    simp [classSum_eq_sum, map_sum, MonoidAlgebra.of_apply]
  have hk : IsIntegral ℤ (classSum k C) :=
    hmap ▸ hZ.map (MonoidAlgebra.mapAlgHom G (Algebra.ofId ℤ k))
  -- integrality inside the center is integrality of the underlying element
  refine (isIntegral_algHom_iff
    ((Subalgebra.center k (MonoidAlgebra k G)).val.restrictScalars ℤ) Subtype.val_injective).mp ?_
  simpa using hk

end TauCeti
