/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.NotReduced
public import TauCeti.Algebra.MonoidAlgebra.SubgroupCharSum
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum

/-!
# Torsion in a character group

The group algebra of a group with torsion cannot be both reduced and connected over a field.
For torsion of order equal to the characteristic, the group algebra contains the familiar
nonzero nilpotent `g - 1`. For torsion of order prime to the characteristic, averaging over the
finite cyclic subgroup produces a nontrivial idempotent.

Consequently, if the group algebra of a commutative group is reduced and has connected prime
spectrum, then the group is torsion-free. This is the algebraic input that distinguishes tori
from general groups of multiplicative type.

## Main declarations

* `TauCeti.groupAlgebraSubgroupAverage`: the normalized sum of a finite subgroup.
* `TauCeti.isIdempotentElem_groupAlgebraSubgroupAverage`: the subgroup average is idempotent.
* `TauCeti.isMulTorsionFree_of_isReduced_monoidAlgebra_of_connectedSpace`: reducedness and
  connectedness of a group algebra force its indexing group to be torsion-free.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This is the character-group calculation used in Layer 4, "Tori: split and non-split", of the
ReductiveGroups roadmap.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

variable {G : Type*} [Group G]

variable (k : Type*) [Field k]

/-- The normalized sum of a finite subgroup: the character sum of the trivial character,
scaled by the inverse of the subgroup order. -/
noncomputable def groupAlgebraSubgroupAverage (P : Subgroup G) [Fintype P] : k[G] :=
  (Fintype.card P : k)⁻¹ • subgroupCharSum (1 : G →* k) P

/-- Left multiplication by a member of a finite subgroup fixes its normalized subgroup
average. -/
@[simp]
theorem single_mul_groupAlgebraSubgroupAverage (P : Subgroup G) [Fintype P] (x : P) :
    MonoidAlgebra.single (x : G) (1 : k) * groupAlgebraSubgroupAverage k P =
      groupAlgebraSubgroupAverage k P := by
  rw [groupAlgebraSubgroupAverage, mul_smul_comm, single_mul_subgroupCharSum]
  simp

/-- The normalized sum of a finite subgroup is idempotent when its cardinality is nonzero in the
base field. -/
theorem isIdempotentElem_groupAlgebraSubgroupAverage (P : Subgroup G) [Fintype P]
    (hP : (Fintype.card P : k) ≠ 0) :
    IsIdempotentElem (groupAlgebraSubgroupAverage k P) := by
  rw [IsIdempotentElem, groupAlgebraSubgroupAverage, smul_mul_smul,
    subgroupCharSum_mul_self, Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul k, smul_smul]
  simp [hP]

/-- A finite subgroup average is nonzero when the subgroup cardinality is nonzero in the base
field. -/
theorem groupAlgebraSubgroupAverage_ne_zero (P : Subgroup G) [Fintype P]
    (hP : (Fintype.card P : k) ≠ 0) :
    groupAlgebraSubgroupAverage k P ≠ 0 := by
  intro hzero
  have h := congrArg (Coalgebra.counit (R := k)) hzero
  simp [groupAlgebraSubgroupAverage, subgroupCharSum_def, hP] at h

/-- The average over a nontrivial finite subgroup is not one. -/
theorem groupAlgebraSubgroupAverage_ne_one (P : Subgroup G) [Fintype P]
    (x : P) (hx : (x : G) ≠ 1) :
    groupAlgebraSubgroupAverage k P ≠ 1 := by
  intro hone
  have hinvariant := single_mul_groupAlgebraSubgroupAverage k P x
  rw [hone, mul_one, MonoidAlgebra.one_def] at hinvariant
  exact hx (MonoidAlgebra.single_left_injective one_ne_zero hinvariant)

/-- If a group algebra over a field is reduced and has connected prime spectrum, then the
indexing commutative group is torsion-free. -/
theorem isMulTorsionFree_of_isReduced_monoidAlgebra_of_connectedSpace
    (k : Type*) [Field k] (G : Type*) [CommGroup G]
    [IsReduced (MonoidAlgebra k G)] [ConnectedSpace (PrimeSpectrum (MonoidAlgebra k G))] :
    IsMulTorsionFree G := by
  rw [isMulTorsionFree_iff_not_isOfFinOrder]
  intro g hg hfinite
  have horder : orderOf g ≠ 0 := orderOf_ne_zero_iff.mpr hfinite
  have horder_one : orderOf g ≠ 1 := by
    exact fun h ↦ hg (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd horder_one
  let y := g ^ (orderOf g / p)
  have hy_order : orderOf y = p := orderOf_pow_orderOf_div horder hp_dvd
  have hy_ne_one : y ≠ 1 := by
    rw [ne_eq, ← orderOf_eq_one_iff, hy_order]
    exact hp.ne_one
  have hy_pow : y ^ p = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hy_order]
  by_cases hchar : (p : k) = 0
  · have _ : Fact p.Prime := ⟨hp⟩
    have _ : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr hchar
    exact not_isReduced_monoidAlgebra (R := k) (G := G) p hy_ne_one hy_pow inferInstance
  · let P := Subgroup.zpowers y
    have hyfinite : IsOfFinOrder y := orderOf_ne_zero_iff.mp (hy_order ▸ hp.ne_zero)
    let _ : Fintype P := Fintype.ofEquiv (Fin (orderOf y)) (finEquivZPowers hyfinite)
    have hcard : Fintype.card P = p := by
      have hcard' : Fintype.card P = orderOf y := by
        simpa using (Fintype.card_congr (finEquivZPowers hyfinite)).symm
      exact hcard'.trans hy_order
    have havg := isIdempotentElem_groupAlgebraSubgroupAverage k P
      (by simpa only [hcard] using hchar)
    rcases eq_zero_or_eq_one_of_isIdempotentElem havg with hzero | hone
    · exact groupAlgebraSubgroupAverage_ne_zero k P
        (by simpa only [hcard] using hchar) hzero
    · exact groupAlgebraSubgroupAverage_ne_one k P ⟨y, Subgroup.mem_zpowers y⟩ hy_ne_one hone

end TauCeti
