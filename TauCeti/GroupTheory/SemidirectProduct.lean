/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Joining a subgroup with a subgroup that normalizes it

Let `H` and `K` be subgroups of a group `G` with `K ≤ Subgroup.normalizer H`. Multiplication then
carries the external semidirect product `H ⋊ K` into `G`, and its image is the join `H ⊔ K`.

Mathlib builds the homomorphism as `SemidirectProduct.monoidHomSubgroup` and computes the carrier
of the join as `Subgroup.coe_mul_of_right_le_normalizer_left`, but records neither the range of
that homomorphism nor the elementwise normal form `g = x * t` that the carrier computation gives.

## Main results

* `TauCeti.SemidirectProduct.range_monoidHomSubgroup`: the range of the semidirect-product
  multiplication homomorphism is `H ⊔ K`.
* `TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left`: an element of `H ⊔ K` is a product of an
  element of `H` followed by an element of `K`.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G] {H K : Subgroup G}

namespace Subgroup

/-- An element of `H ⊔ K` is a product of an element of `H` followed by an element of `K`, as soon
as `K` normalizes `H`. -/
theorem mem_sup_of_right_le_normalizer_left (hLE : K ≤ Subgroup.normalizer (H : Set G)) {g : G} :
    g ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ t ∈ K, g = x * t := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H K hLE, Set.mem_mul]
  simp [eq_comm]

end Subgroup

namespace SemidirectProduct

/-- Multiplication from the semidirect product of a subgroup with a subgroup normalizing it is onto
the join of the two subgroups. -/
theorem range_monoidHomSubgroup (hLE : K ≤ Subgroup.normalizer (H : Set G)) :
    (SemidirectProduct.monoidHomSubgroup hLE).range = H ⊔ K := by
  refine le_antisymm ?_ (sup_le (fun x hx => ⟨SemidirectProduct.inl ⟨x, hx⟩, by simp⟩)
    fun t ht => ⟨SemidirectProduct.inr ⟨t, ht⟩, by simp⟩)
  rintro _ ⟨x, rfl⟩
  rw [SemidirectProduct.monoidHomSubgroup_apply]
  exact Subgroup.mul_mem_sup x.1.2 x.2.2

end SemidirectProduct

end TauCeti
