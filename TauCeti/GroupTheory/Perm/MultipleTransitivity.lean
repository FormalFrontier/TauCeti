/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan

/-!
# Long cycles and double transitivity

A transitive permutation group containing a cycle on all but one point is doubly transitive. The
missing point is the unique fixed point of the cycle. Its stabilizer contains the cycle and is
therefore transitive on the complement; the usual point-stabilizer criterion then gives double
transitivity of the original action.

## Main results

* `TauCeti.existsUnique_fixedPoint_of_card_support_add_one_eq`: a permutation moving all but
  one point has a unique fixed point.
* `TauCeti.is_two_pretransitive_of_isCycle_mem`: a transitive permutation group that
  contains such a cycle is doubly transitive.

The second result is one of the generic recognition theorems in Layer 1 of
`TauCetiRoadmap/PolynomialGaloisGroups/README.md`. It is used there both in the classification of
transitive groups of degree at most five and in the three-prime construction of polynomials with
full symmetric Galois group.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, §2.1.
* H. Wielandt, *Finite Permutation Groups*, Chapter II.
-/

public section

namespace TauCeti

open MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A permutation whose support has one fewer element than its finite domain has a unique fixed
point. -/
theorem existsUnique_fixedPoint_of_card_support_add_one_eq (σ : Equiv.Perm α)
    (hcard : σ.support.card + 1 = Fintype.card α) :
    ∃! x : α, σ x = x := by
  have hcompl : σ.supportᶜ.card = 1 := by
    rw [Finset.card_compl]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨x, ?_, fun y hy => ?_⟩
  · apply Equiv.Perm.notMem_support.mp
    have : x ∈ σ.supportᶜ := by simp [hx]
    simpa only [Finset.mem_compl] using this
  · have hy' : y ∉ σ.support := by simpa only [Equiv.Perm.notMem_support] using hy
    have hycompl : y ∈ σ.supportᶜ := Finset.mem_compl.mpr hy'
    simpa [hx] using hycompl

/-- A transitive subgroup of a finite symmetric group that contains a cycle moving all but one
point is doubly transitive. -/
theorem is_two_pretransitive_of_isCycle_mem
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α] {σ : Equiv.Perm α}
    (hσ : σ.IsCycle) (hσG : σ ∈ G)
    (hcard : σ.support.card + 1 = Fintype.card α) :
    IsMultiplyPretransitive G α 2 := by
  obtain ⟨x, hx, huniq⟩ :=
    existsUnique_fixedPoint_of_card_support_add_one_eq σ hcard
  have hcompl : ((σ.support : Set α)ᶜ) = {x} := by
    ext y
    simp only [Set.mem_compl_iff, Finset.mem_coe, Equiv.Perm.mem_support,
      Set.mem_singleton_iff]
    exact ⟨fun hy => huniq y (not_not.mp hy), fun hy hmove => hmove (hy ▸ hx)⟩
  have htrans :
      IsPretransitive (fixingSubgroup G ({x} : Set α))
        (SubMulAction.ofFixingSubgroup G ({x} : Set α)) := by
    rw [← hcompl]
    exact Equiv.Perm.isPretransitive_of_isCycle_mem hσ hσG
  rw [SubMulAction.ofStabilizer.isMultiplyPretransitive (a := x)]
  rw [is_one_pretransitive_iff]
  exact IsPretransitive.of_surjective_map
    SubMulAction.ofFixingSubgroup_of_singleton_bijective.surjective htrans

end TauCeti
