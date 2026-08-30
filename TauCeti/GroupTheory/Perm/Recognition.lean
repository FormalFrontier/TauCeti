/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Recognition of a full cycle in prime degree

This file supplies the first prime-degree recognition step for
`TauCetiRoadmap/PolynomialGaloisGroups/README.md`: a transitive subgroup of a finite symmetric
group whose degree is prime contains a full cycle. The proof combines orbit--stabilizer with
Cauchy's theorem and the permutation-group criterion that an element of prime order in prime
degree is a cycle.
-/

public section

namespace TauCeti

open MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A transitive permutation group of prime degree contains a full cycle.

The returned permutation has order and support cardinality equal to the degree, so its support
is all of `α`. This is intended as a prime-degree recognition input for the low-degree
classification and for the prime-degree branch of the `Sₙ` realization argument.
-/
theorem exists_isCycle_mem_of_isPretransitive_of_prime_card
    {G : Subgroup (Equiv.Perm α)} (hG : IsPretransitive G α)
    (hp : Nat.Prime (Fintype.card α)) :
    ∃ g : Equiv.Perm α, g ∈ G ∧ g.IsCycle ∧ g.support = Finset.univ := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let a : α := Classical.choice (Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hp.ne_zero))
  have horbit : orbit G a = Set.univ :=
    (isPretransitive_iff_orbit_eq_univ a).mp hG
  have hcard : Fintype.card α ∣ Fintype.card G := by
    refine ⟨Fintype.card (stabilizer G a), ?_⟩
    simpa [horbit, Nat.mul_comm] using
      (card_orbit_mul_card_stabilizer_eq_card_group (G := G) a).symm
  let _ : Fact (Fintype.card α).Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) hcard
  have horder : orderOf (g : Equiv.Perm α) = Fintype.card α :=
    (Subgroup.orderOf_coe g).trans hg
  have hcycle : (g : Equiv.Perm α).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order'' hp horder
  have hsupport : (g : Equiv.Perm α).support = Finset.univ :=
    Finset.eq_univ_of_card (g : Equiv.Perm α).support (hcycle.orderOf.symm.trans horder)
  exact ⟨g, g.property, hcycle, hsupport⟩

end TauCeti
