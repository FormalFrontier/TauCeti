/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.ChevalleyRelations
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Generation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Weyl

/-!
# Generating long and sum roots in the symplectic group

This file develops the root-subgroup generation step for the standard type-`C` symplectic group
beyond its type-`A` subsystem of difference roots. Over an arbitrary commutative ring, the
difference-root subgroups and one pair of opposite long-root subgroups generate every long and sum
root subgroup.

The difference-root word

```text
n_{i,j} = x_{eᵢ-eⱼ}(1) x_{eⱼ-eᵢ}(-1) x_{eᵢ-eⱼ}(1)
```

represents the Weyl reflection exchanging `i` and `j`, so conjugation by it carries
`x_{±2eⱼ}(c)` to `x_{±2eᵢ}(c)`. The sum roots are then isolated from the multiply-laced
Chevalley commutator relations. In particular, the numbered adjacent difference roots and the
final long root generate every root subgroup in all characteristics, including characteristic
two.

## Main results

* `TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit_mem_of_difference_of_long` and its
  negative analogue propagate one long-root subgroup to every index by Weyl conjugation.
* `TauCeti.GLSymplecticFin.positiveSumShortRootUnit_mem_of_difference_of_long` and its negative
  analogue generate the two sum-root families.
* `TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_apply_mem_of_difference_of_long` packages the
  result for every standard symplectic root subgroup.
* `TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_apply_mem_of_adjacent_of_long` reduces the
  hypotheses further to the positive and negative simple-root families.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2.
* R. Steinberg, *Lectures on Chevalley Groups* (1968), §§3--4.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: it supplies every root subgroup required for the
reverse inclusion of the full-weight type-`C` carrier in the standard symplectic group. Removing
the former invertibility-of-two hypothesis is necessary for the characteristic-two type-`C`
branch consumed by milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti.GLSymplecticFin

universe u

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

/-- If a subgroup contains every difference-root element and the positive long-root subgroup at
`r`, then it contains every positive long-root element. -/
theorem positiveLongRootTransvectionUnit_mem_of_difference_of_long
    (H : Subgroup (GLSymplecticFin m R)) (r : Fin m)
    (hdifference : ∀ {i j : Fin m} (hij : i ≠ j) (c : R),
      differenceShortRootUnit hij c ∈ H)
    (hpivot : ∀ c : R, positiveLongRootTransvectionUnit r c ∈ H)
    (i : Fin m) (c : R) : positiveLongRootTransvectionUnit i c ∈ H := by
  by_cases hir : i = r
  · subst i
    exact hpivot c
  · let w := differenceShortRootWeylElement (R := R) hir
    have hw : w ∈ H := differenceShortRootWeylElement_mem H hir
      (hdifference hir) (hdifference (Ne.symm hir))
    have hconj := H.mul_mem (H.mul_mem hw (hpivot c)) (H.inv_mem hw)
    simpa only [w, differenceShortRootWeylElement_inv,
      differenceShortRootWeylElement_mul_positiveLongRootTransvectionUnit_mul_inv] using hconj

/-- If a subgroup contains every difference-root element and the negative long-root subgroup at
`r`, then it contains every negative long-root element. -/
theorem negativeLongRootTransvectionUnit_mem_of_difference_of_long
    (H : Subgroup (GLSymplecticFin m R)) (r : Fin m)
    (hdifference : ∀ {i j : Fin m} (hij : i ≠ j) (c : R),
      differenceShortRootUnit hij c ∈ H)
    (hpivot : ∀ c : R, negativeLongRootTransvectionUnit r c ∈ H)
    (i : Fin m) (c : R) : negativeLongRootTransvectionUnit i c ∈ H := by
  by_cases hir : i = r
  · subst i
    exact hpivot c
  · let w := differenceShortRootWeylElement (R := R) hir
    have hw : w ∈ H := differenceShortRootWeylElement_mem H hir
      (hdifference hir) (hdifference (Ne.symm hir))
    have hconj := H.mul_mem (H.mul_mem hw (hpivot c)) (H.inv_mem hw)
    simpa only [w, differenceShortRootWeylElement_inv,
      differenceShortRootWeylElement_mul_negativeLongRootTransvectionUnit_mul_inv] using hconj

/-- A positive-sum short-root element lies in a subgroup containing the corresponding
difference-root element at parameter `1` and the two long-root elements used to isolate it. -/
theorem positiveSumShortRootUnit_mem_of_difference_of_long
    (H : Subgroup (GLSymplecticFin m R)) (hij : i ≠ j) (c : R)
    (hdifference : differenceShortRootUnit hij 1 ∈ H)
    (hlongj : positiveLongRootTransvectionUnit j c ∈ H)
    (hlongi : positiveLongRootTransvectionUnit i c ∈ H) :
    positiveSumShortRootUnit hij c ∈ H := by
  have hproduct := H.commutator_le_self
    (Subgroup.commutator_mem_commutator hdifference hlongj)
  rw [commutatorElement_differenceShortRootUnit_positiveLongRootTransvectionUnit] at hproduct
  have hisolate := H.mul_mem hproduct (H.inv_mem hlongi)
  simpa only [one_mul, one_pow, mul_assoc, mul_inv_cancel, mul_one] using hisolate

/-- A negative-sum short-root element lies in a subgroup containing the corresponding
difference-root element at parameter `1` and the two long-root elements used to isolate it. -/
theorem negativeSumShortRootUnit_mem_of_difference_of_long
    (H : Subgroup (GLSymplecticFin m R)) (hij : i ≠ j) (c : R)
    (hdifference : differenceShortRootUnit hij 1 ∈ H)
    (hlongi : negativeLongRootTransvectionUnit i (-c) ∈ H)
    (hlongj : negativeLongRootTransvectionUnit j (-c) ∈ H) :
    negativeSumShortRootUnit hij c ∈ H := by
  have hproduct := H.commutator_le_self
    (Subgroup.commutator_mem_commutator hdifference hlongi)
  rw [commutatorElement_differenceShortRootUnit_negativeLongRootTransvectionUnit] at hproduct
  have hisolate := H.mul_mem hproduct (H.inv_mem hlongj)
  simpa only [one_mul, one_pow, neg_neg, mul_assoc, mul_inv_cancel, mul_one] using hisolate

namespace RootSubgroupIndex

/-- **Difference roots and one opposite pair of long-root subgroups generate every symplectic root
subgroup.** More precisely, if `H` contains every difference-root element and both long-root
subgroups at one index, then the value of every root one-parameter subgroup lies in `H`. -/
theorem hom_apply_mem_of_difference_of_long
    (H : Subgroup (GLSymplecticFin m R)) (r : Fin m)
    (hdifference : ∀ {i j : Fin m} (hij : i ≠ j) (c : R),
      differenceShortRootUnit hij c ∈ H)
    (hpositive : ∀ c : R, positiveLongRootTransvectionUnit r c ∈ H)
    (hnegative : ∀ c : R, negativeLongRootTransvectionUnit r c ∈ H)
    (root : RootSubgroupIndex m) (c : Multiplicative R) : root.hom c ∈ H := by
  have hp (i : Fin m) (a : R) : positiveLongRootTransvectionUnit i a ∈ H :=
    positiveLongRootTransvectionUnit_mem_of_difference_of_long
      H r hdifference hpositive i a
  have hn (i : Fin m) (a : R) : negativeLongRootTransvectionUnit i a ∈ H :=
    negativeLongRootTransvectionUnit_mem_of_difference_of_long
      H r hdifference hnegative i a
  cases root with
  | positiveLong i =>
      simpa only [hom_positiveLong, positiveLongRootTransvectionHom_apply] using hp i c.toAdd
  | negativeLong i =>
      simpa only [hom_negativeLong, negativeLongRootTransvectionHom_apply] using hn i c.toAdd
  | difference i j hij =>
      simpa only [hom_difference, differenceShortRootHom_apply] using hdifference hij c.toAdd
  | positiveSum i j hij =>
      simpa only [hom_positiveSum, positiveSumShortRootHom_apply] using
        positiveSumShortRootUnit_mem_of_difference_of_long H hij.ne c.toAdd
          (hdifference hij.ne 1) (hp j c.toAdd) (hp i c.toAdd)
  | negativeSum i j hij =>
      simpa only [hom_negativeSum, negativeSumShortRootHom_apply] using
        negativeSumShortRootUnit_mem_of_difference_of_long H hij.ne c.toAdd
          (hdifference hij.ne 1) (hn i (-c.toAdd)) (hn j (-c.toAdd))

/-- **The positive and negative simple-root families generate every standard symplectic root
subgroup.** It is enough for `H` to contain the two orientations of every adjacent difference
root and one pair of opposite long-root subgroups. This formulation matches the numbered simple
roots of type `C` and holds over every commutative ring. -/
theorem hom_apply_mem_of_adjacent_of_long
    (H : Subgroup (GLSymplecticFin m R)) (r : Fin m)
    (hadjacent : ∀ {i j : Fin m} (hij : i ≠ j) (c : R),
      i.val + 1 = j.val ∨ j.val + 1 = i.val → differenceShortRootUnit hij c ∈ H)
    (hpositive : ∀ c : R, positiveLongRootTransvectionUnit r c ∈ H)
    (hnegative : ∀ c : R, negativeLongRootTransvectionUnit r c ∈ H)
    (root : RootSubgroupIndex m) (c : Multiplicative R) : root.hom c ∈ H := by
  apply hom_apply_mem_of_difference_of_long H r _ hpositive hnegative
  exact differenceShortRootUnit_mem_of_adjacent H hadjacent

end RootSubgroupIndex

end TauCeti.GLSymplecticFin
