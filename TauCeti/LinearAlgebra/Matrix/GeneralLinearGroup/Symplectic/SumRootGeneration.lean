/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.ChevalleyRelations

/-!
# Generating the sum-root subgroups of the symplectic group

The standard type-`C_m` root system has short roots `eᵢ - eⱼ`, `eᵢ + eⱼ`, and
`-eᵢ - eⱼ`, together with the long roots `±2eᵢ`. This file uses the multiply-laced
Chevalley relations to recover the two sum-root families from the difference-root and long-root
families. For distinct `i` and `j`, specializing the positive relation at parameter one gives

```text
⁅x_{eᵢ-eⱼ}(1), x_{2eⱼ}(c)⁆ = x_{eᵢ+eⱼ}(c) x_{2eᵢ}(c),
```

and the negative relation at `-c` gives the corresponding formula for `-eᵢ-eⱼ`. Thus a
subgroup containing every difference-root and long-root element contains every root element of
the standard symplectic realization. The argument uses no division, so it works over every
commutative ring, including characteristic two.

## Main results

* `TauCeti.GLSymplecticFin.positiveSumShortRootUnit_mem_of_difference_long`: a positive sum-root
  element belongs to a subgroup containing the three elements in the specialized commutator
  relation.
* `TauCeti.GLSymplecticFin.negativeSumShortRootUnit_mem_of_difference_long`: the parallel negative
  result.
* `TauCeti.GLSymplecticFin.rootSubgroupHom_mem_of_difference_long`: difference-root and long-root
  families generate every root family.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2.
* R. Steinberg, *Lectures on Chevalley Groups* (1968), §§3--4.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: it is the sum-root generation step needed to identify
the explicit full-weight type-`C` carrier with the standard symplectic group on field-valued
points. That identification is consumed by the `C_n(q)` branch of milestone L0 in
`TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

open scoped commutatorElement

namespace TauCeti.GLSymplecticFin

universe u

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

/-- A positive sum-root element lies in any subgroup containing the parameter-one difference-root
element and the two positive long-root elements occurring in its Chevalley commutator formula. -/
theorem positiveSumShortRootUnit_mem_of_difference_long
    (H : Subgroup (GLSymplecticFin m R)) (hij : i ≠ j) (c : R)
    (hdifference : differenceShortRootUnit hij 1 ∈ H)
    (hsource : positiveLongRootTransvectionUnit j c ∈ H)
    (htarget : positiveLongRootTransvectionUnit i c ∈ H) :
    positiveSumShortRootUnit hij c ∈ H := by
  have hcomm :
      ⁅differenceShortRootUnit hij (1 : R), positiveLongRootTransvectionUnit j c⁆ ∈ H :=
    by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hdifference hsource) (H.inv_mem hdifference))
        (H.inv_mem hsource)
  rw [commutatorElement_differenceShortRootUnit_positiveLongRootTransvectionUnit,
    one_mul, one_pow, one_mul] at hcomm
  exact (H.mul_mem_cancel_right htarget).mp hcomm

/-- A negative sum-root element lies in any subgroup containing the parameter-one difference-root
element and the two negative long-root elements occurring in its Chevalley commutator formula. -/
theorem negativeSumShortRootUnit_mem_of_difference_long
    (H : Subgroup (GLSymplecticFin m R)) (hij : i ≠ j) (c : R)
    (hdifference : differenceShortRootUnit hij 1 ∈ H)
    (hsource : negativeLongRootTransvectionUnit i (-c) ∈ H)
    (htarget : negativeLongRootTransvectionUnit j (-c) ∈ H) :
    negativeSumShortRootUnit hij c ∈ H := by
  have hcomm :
      ⁅differenceShortRootUnit hij (1 : R), negativeLongRootTransvectionUnit i (-c)⁆ ∈ H :=
    by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hdifference hsource) (H.inv_mem hdifference))
        (H.inv_mem hsource)
  rw [commutatorElement_differenceShortRootUnit_negativeLongRootTransvectionUnit,
    one_mul, neg_neg, one_pow, one_mul] at hcomm
  exact (H.mul_mem_cancel_right htarget).mp hcomm

/-- If a subgroup of the standard symplectic group contains every difference-root element and
every positive and negative long-root element, then it contains every standard root-subgroup
element. This is valid over an arbitrary commutative ring. -/
theorem rootSubgroupHom_mem_of_difference_long
    (H : Subgroup (GLSymplecticFin m R))
    (hdifference : ∀ {i j : Fin m} (hij : i ≠ j) (c : R),
      differenceShortRootUnit hij c ∈ H)
    (hpositiveLong : ∀ (i : Fin m) (c : R), positiveLongRootTransvectionUnit i c ∈ H)
    (hnegativeLong : ∀ (i : Fin m) (c : R), negativeLongRootTransvectionUnit i c ∈ H)
    (root : RootSubgroupIndex m) (c : Multiplicative R) :
    root.hom c ∈ H := by
  cases root with
  | positiveLong i =>
      rw [RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply]
      exact hpositiveLong i c.toAdd
  | negativeLong i =>
      rw [RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply]
      exact hnegativeLong i c.toAdd
  | difference i j hij =>
      rw [← RootSubgroupIndex.short_difference i j hij, RootSubgroupIndex.hom_short,
        ShortRootFamily.hom_difference,
        differenceShortRootHom_apply]
      exact hdifference hij c.toAdd
  | positiveSum i j hij =>
      rw [← RootSubgroupIndex.short_positiveSum_of_lt i j hij,
        RootSubgroupIndex.hom_short, ShortRootFamily.hom_positiveSum,
        positiveSumShortRootHom_apply]
      exact positiveSumShortRootUnit_mem_of_difference_long H hij.ne c.toAdd
        (hdifference hij.ne 1) (hpositiveLong j c.toAdd) (hpositiveLong i c.toAdd)
  | negativeSum i j hij =>
      rw [← RootSubgroupIndex.short_negativeSum_of_lt i j hij,
        RootSubgroupIndex.hom_short, ShortRootFamily.hom_negativeSum,
        negativeSumShortRootHom_apply]
      exact negativeSumShortRootUnit_mem_of_difference_long H hij.ne c.toAdd
        (hdifference hij.ne 1) (hnegativeLong i (-c.toAdd)) (hnegativeLong j (-c.toAdd))

end TauCeti.GLSymplecticFin
