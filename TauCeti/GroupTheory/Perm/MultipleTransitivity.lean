/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import TauCeti.GroupTheory.Perm.Basic

/-!
# Long cycles and double transitivity

A transitive permutation group containing a cycle on all but one point is doubly transitive. The
missing point is the unique fixed point of the cycle. Its stabilizer contains the cycle and is
therefore transitive on the complement; the usual point-stabilizer criterion then gives double
transitivity of the original action.

## Main results

* `TauCeti.card_support_add_one_eq_card_iff_existsUnique_fixedPoint`: a permutation moves all but
  one point exactly when it has a unique fixed point.
* `TauCeti.is_two_pretransitive_of_isCycle_mem_of_card_support_add_one_eq_card`: a transitive
  permutation group that contains such a cycle is doubly transitive.
* `TauCeti.isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq_card`: such a group is
  primitive.

The second result is one of the generic recognition theorems in Layer 1 of
`TauCetiRoadmap/PolynomialGaloisGroups/README.md`. It is used there both in the classification of
transitive groups of degree at most five and in the three-prime construction of polynomials with
full symmetric Galois group.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, §2.1.
* H. Wielandt, *Finite Permutation Groups*, Chapter II.

The point-stabilizer step is adapted from `Mathlib/GroupTheory/GroupAction/Jordan.lean`, by Antoine
Chambert-Loir; transitivity on the support uses that file's
`Equiv.Perm.isPretransitive_of_isCycle_mem`.
-/

public section

namespace TauCeti

open MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A transitive subgroup of a finite symmetric group that contains a cycle moving all but one
point is doubly transitive. -/
theorem is_two_pretransitive_of_isCycle_mem_of_card_support_add_one_eq_card
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α] {σ : Equiv.Perm α}
    (hσ : σ.IsCycle) (hσG : σ ∈ G)
    (hcard : σ.support.card + 1 = Fintype.card α) :
    IsMultiplyPretransitive G α 2 := by
  have hcomplCard : σ.supportᶜ.card = 1 := by
    rw [Finset.card_compl]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcomplCard
  have hcompl : ((σ.support : Set α)ᶜ) = {x} := by
    rw [← Finset.coe_compl, hx, Finset.coe_singleton]
  have htrans :
      IsPretransitive (fixingSubgroup G ({x} : Set α))
        (SubMulAction.ofFixingSubgroup G ({x} : Set α)) := by
    rw [← hcompl]
    exact Equiv.Perm.isPretransitive_of_isCycle_mem hσ hσG
  rw [SubMulAction.ofStabilizer.isMultiplyPretransitive (a := x)]
  rw [is_one_pretransitive_iff]
  exact IsPretransitive.of_surjective_map
    SubMulAction.ofFixingSubgroup_of_singleton_bijective.surjective htrans

/-- A transitive subgroup of a finite symmetric group that contains a cycle moving all but one
point is primitive. -/
theorem isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq_card
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α] {σ : Equiv.Perm α}
    (hσ : σ.IsCycle) (hσG : σ ∈ G)
    (hcard : σ.support.card + 1 = Fintype.card α) :
    IsPreprimitive G α :=
  isPreprimitive_of_is_two_pretransitive
    (is_two_pretransitive_of_isCycle_mem_of_card_support_add_one_eq_card
      G hσ hσG hcard)

end TauCeti
