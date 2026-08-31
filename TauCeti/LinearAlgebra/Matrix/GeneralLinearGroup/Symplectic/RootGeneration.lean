/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.ChevalleyRelations

/-!
# Generating long and sum roots in the symplectic group

This file develops the root-subgroup generation step for the standard type-`C` symplectic group
beyond its type-`A` subsystem of difference roots. Over a commutative ring in which `2` is a unit,
the difference-root subgroups and one pair of opposite long-root subgroups generate every long and
sum root subgroup.

The long roots are extracted from the multiply-laced Chevalley relation by comparing the parameters
`1` and `-1`:

```text
⁅x_{eᵢ-eⱼ}(1),  x_{2eⱼ}(t)⁆  = x_{eᵢ+eⱼ}(t) x_{2eᵢ}(t),
⁅x_{eᵢ-eⱼ}(-1), x_{2eⱼ}(-t)⁆ = x_{eᵢ+eⱼ}(t) x_{2eᵢ}(-t).
```

Their quotient is `x_{2eᵢ}(2t)`, since the displayed sum-root subgroup commutes with the long
root subgroup. Invertibility of `2` makes this every parameter. The negative roots follow from the
opposite relation, and the sum roots are then isolated from either commutator formula.

## Main results

* `TauCeti.GLSymplecticFin.positiveLongRootTransvectionUnit_mem_of_difference_of_long` and its
  negative analogue propagate one long-root subgroup to every index.
* `TauCeti.GLSymplecticFin.positiveSumShortRootUnit_mem_of_difference_of_long` and its negative
  analogue generate the two sum-root families.
* `TauCeti.GLSymplecticFin.RootSubgroupIndex.hom_apply_mem_of_difference_of_long` packages the
  result for every standard symplectic root subgroup.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2.
* R. Steinberg, *Lectures on Chevalley Groups* (1968), §§3--4.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: together with generation of all difference roots from
the numbered adjacent roots, it supplies every root subgroup required for the reverse inclusion of
the full-weight type-`C` carrier in the standard symplectic group. The restriction that `2` be a
unit matches the odd-characteristic type-`C` branch of milestone L0 in
`TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti.GLSymplecticFin

universe u

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

private theorem commute_positiveSumShortRootUnit_positiveLongRootTransvectionUnit
    (hij : i ≠ j) (a b : R) :
  Commute (positiveSumShortRootUnit hij a) (positiveLongRootTransvectionUnit i b) := by
  have hIL : Commute (transvectionUnit (finSumFinEquiv_inl_ne_inr i j) a)
      (transvectionUnit (finSumFinEquiv_inl_ne_inr i i) b) :=
    commute_transvectionUnit (finSumFinEquiv_inl_ne_inr i j)
      (finSumFinEquiv_inl_ne_inr i i) (finSumFinEquiv_inr_ne_inl j i)
      (finSumFinEquiv_inr_ne_inl i i) a b
  have hJL : Commute (transvectionUnit (finSumFinEquiv_inl_ne_inr j i) a)
      (transvectionUnit (finSumFinEquiv_inl_ne_inr i i) b) :=
    commute_transvectionUnit (finSumFinEquiv_inl_ne_inr j i)
      (finSumFinEquiv_inl_ne_inr i i) (finSumFinEquiv_inr_ne_inl i i)
      (finSumFinEquiv_inr_ne_inl i j) a b
  have hambient :
      (positiveSumShortRootUnit hij a : GL (Fin (m + m)) R) *
          (positiveLongRootTransvectionUnit i b : GL (Fin (m + m)) R) =
        (positiveLongRootTransvectionUnit i b : GL (Fin (m + m)) R) *
          (positiveSumShortRootUnit hij a : GL (Fin (m + m)) R) := by
    rw [coe_positiveSumShortRootUnit, coe_positiveLongRootTransvectionUnit]
    exact hIL.mul_left hJL
  exact (GLSymplecticFin m R).subtype_injective hambient

private theorem commute_negativeSumShortRootUnit_negativeLongRootTransvectionUnit
    (hij : i ≠ j) (a b : R) :
    Commute (negativeSumShortRootUnit hij a) (negativeLongRootTransvectionUnit j b) := by
  have hIL : Commute (transvectionUnit (finSumFinEquiv_inr_ne_inl i j) a)
      (transvectionUnit (finSumFinEquiv_inr_ne_inl j j) b) :=
    commute_transvectionUnit (finSumFinEquiv_inr_ne_inl i j)
      (finSumFinEquiv_inr_ne_inl j j) (finSumFinEquiv_inl_ne_inr j j)
      (finSumFinEquiv_inl_ne_inr j i) a b
  have hJL : Commute (transvectionUnit (finSumFinEquiv_inr_ne_inl j i) a)
      (transvectionUnit (finSumFinEquiv_inr_ne_inl j j) b) :=
    commute_transvectionUnit (finSumFinEquiv_inr_ne_inl j i)
      (finSumFinEquiv_inr_ne_inl j j) (finSumFinEquiv_inl_ne_inr i j)
      (finSumFinEquiv_inl_ne_inr j j) a b
  have hambient :
      (negativeSumShortRootUnit hij a : GL (Fin (m + m)) R) *
          (negativeLongRootTransvectionUnit j b : GL (Fin (m + m)) R) =
        (negativeLongRootTransvectionUnit j b : GL (Fin (m + m)) R) *
          (negativeSumShortRootUnit hij a : GL (Fin (m + m)) R) := by
    rw [coe_negativeSumShortRootUnit, coe_negativeLongRootTransvectionUnit]
    exact hIL.mul_left hJL
  exact (GLSymplecticFin m R).subtype_injective hambient

/-- If a subgroup contains every difference-root element pointing to `r` and the positive
long-root subgroup at `r`, then it contains every positive long-root element, provided `2` is
invertible in the coefficient ring. -/
theorem positiveLongRootTransvectionUnit_mem_of_difference_of_long
    (H : Subgroup (GLSymplecticFin m R)) (h2 : IsUnit (2 : R)) (r : Fin m)
    (hdifference : ∀ {i : Fin m} (hir : i ≠ r) (c : R),
      differenceShortRootUnit hir c ∈ H)
    (hpivot : ∀ c : R, positiveLongRootTransvectionUnit r c ∈ H)
    (i : Fin m) (c : R) : positiveLongRootTransvectionUnit i c ∈ H := by
  by_cases hir : i = r
  · subst i
    exact hpivot c
  · obtain ⟨u, hu⟩ := h2
    let t : R := ((u⁻¹ : Rˣ) : R) * c
    have ht : t + t = c := by
      dsimp only [t]
      rw [← two_mul, ← hu]
      simp
    have hfirst :
        positiveSumShortRootUnit hir t * positiveLongRootTransvectionUnit i t ∈ H := by
      have hmem := H.commutator_le_self
        (Subgroup.commutator_mem_commutator (hdifference hir 1) (hpivot t))
      rw [commutatorElement_differenceShortRootUnit_positiveLongRootTransvectionUnit] at hmem
      simpa using hmem
    have hsecond :
        positiveSumShortRootUnit hir t * positiveLongRootTransvectionUnit i (-t) ∈ H := by
      have hmem := H.commutator_le_self
        (Subgroup.commutator_mem_commutator (hdifference hir (-1)) (hpivot (-t)))
      rw [commutatorElement_differenceShortRootUnit_positiveLongRootTransvectionUnit] at hmem
      simpa using hmem
    have hquotient := H.mul_mem hfirst (H.inv_mem hsecond)
    have heq :
        (positiveSumShortRootUnit hir t * positiveLongRootTransvectionUnit i t) *
            (positiveSumShortRootUnit hir t *
              positiveLongRootTransvectionUnit i (-t))⁻¹ =
          positiveLongRootTransvectionUnit i c := by
      calc
        _ = positiveSumShortRootUnit hir t *
              (positiveLongRootTransvectionUnit i t *
                positiveLongRootTransvectionUnit i t) *
              (positiveSumShortRootUnit hir t)⁻¹ := by
            rw [_root_.mul_inv_rev, positiveLongRootTransvectionUnit_inv, neg_neg]
            group
        _ = positiveSumShortRootUnit hir t *
              positiveLongRootTransvectionUnit i (t + t) *
              (positiveSumShortRootUnit hir t)⁻¹ := by
            rw [← positiveLongRootTransvectionUnit_add]
        _ = positiveLongRootTransvectionUnit i (t + t) := by
            rw [(commute_positiveSumShortRootUnit_positiveLongRootTransvectionUnit
              hir t (t + t)).eq]
            group
        _ = positiveLongRootTransvectionUnit i c := by rw [ht]
    rwa [heq] at hquotient

/-- If a subgroup contains every difference-root element pointing from `r` and the negative
long-root subgroup at `r`, then it contains every negative long-root element, provided `2` is
invertible in the coefficient ring. -/
theorem negativeLongRootTransvectionUnit_mem_of_difference_of_long
    (H : Subgroup (GLSymplecticFin m R)) (h2 : IsUnit (2 : R)) (r : Fin m)
    (hdifference : ∀ {i : Fin m} (hri : r ≠ i) (c : R),
      differenceShortRootUnit hri c ∈ H)
    (hpivot : ∀ c : R, negativeLongRootTransvectionUnit r c ∈ H)
    (i : Fin m) (c : R) : negativeLongRootTransvectionUnit i c ∈ H := by
  by_cases hir : i = r
  · subst i
    exact hpivot c
  · obtain ⟨u, hu⟩ := h2
    let t : R := ((u⁻¹ : Rˣ) : R) * c
    have ht : t + t = c := by
      dsimp only [t]
      rw [← two_mul, ← hu]
      simp
    have hri : r ≠ i := Ne.symm hir
    have hfirst :
        negativeSumShortRootUnit hri (-t) * negativeLongRootTransvectionUnit i t ∈ H := by
      have hmem := H.commutator_le_self
        (Subgroup.commutator_mem_commutator (hdifference hri 1) (hpivot t))
      rw [commutatorElement_differenceShortRootUnit_negativeLongRootTransvectionUnit] at hmem
      simpa using hmem
    have hsecond :
        negativeSumShortRootUnit hri (-t) * negativeLongRootTransvectionUnit i (-t) ∈ H := by
      have hmem := H.commutator_le_self
        (Subgroup.commutator_mem_commutator (hdifference hri (-1)) (hpivot (-t)))
      rw [commutatorElement_differenceShortRootUnit_negativeLongRootTransvectionUnit] at hmem
      simpa using hmem
    have hquotient := H.mul_mem hfirst (H.inv_mem hsecond)
    have heq :
        (negativeSumShortRootUnit hri (-t) * negativeLongRootTransvectionUnit i t) *
            (negativeSumShortRootUnit hri (-t) *
              negativeLongRootTransvectionUnit i (-t))⁻¹ =
          negativeLongRootTransvectionUnit i c := by
      calc
        _ = negativeSumShortRootUnit hri (-t) *
              (negativeLongRootTransvectionUnit i t *
                negativeLongRootTransvectionUnit i t) *
              (negativeSumShortRootUnit hri (-t))⁻¹ := by
            rw [_root_.mul_inv_rev, negativeLongRootTransvectionUnit_inv, neg_neg]
            group
        _ = negativeSumShortRootUnit hri (-t) *
              negativeLongRootTransvectionUnit i (t + t) *
              (negativeSumShortRootUnit hri (-t))⁻¹ := by
            rw [← negativeLongRootTransvectionUnit_add]
        _ = negativeLongRootTransvectionUnit i (t + t) := by
            rw [(commute_negativeSumShortRootUnit_negativeLongRootTransvectionUnit
              hri (-t) (t + t)).eq]
            group
        _ = negativeLongRootTransvectionUnit i c := by rw [ht]
    rwa [heq] at hquotient

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
subgroup when `2` is invertible.** More precisely, if `H` contains every difference-root element
and both long-root subgroups at one index, then the value of every root one-parameter subgroup lies
in `H`. -/
theorem hom_apply_mem_of_difference_of_long
    (H : Subgroup (GLSymplecticFin m R)) (h2 : IsUnit (2 : R)) (r : Fin m)
    (hdifference : ∀ {i j : Fin m} (hij : i ≠ j) (c : R),
      differenceShortRootUnit hij c ∈ H)
    (hpositive : ∀ c : R, positiveLongRootTransvectionUnit r c ∈ H)
    (hnegative : ∀ c : R, negativeLongRootTransvectionUnit r c ∈ H)
    (root : RootSubgroupIndex m) (c : Multiplicative R) : root.hom c ∈ H := by
  have hp (i : Fin m) (a : R) : positiveLongRootTransvectionUnit i a ∈ H :=
    positiveLongRootTransvectionUnit_mem_of_difference_of_long
      H h2 r hdifference hpositive i a
  have hn (i : Fin m) (a : R) : negativeLongRootTransvectionUnit i a ∈ H :=
    negativeLongRootTransvectionUnit_mem_of_difference_of_long
      H h2 r hdifference hnegative i a
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

end RootSubgroupIndex

end TauCeti.GLSymplecticFin
