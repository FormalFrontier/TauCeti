/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Consequences of the index formula

The preimage `H.comap f` of a finite-index subgroup along a group homomorphism again has finite
index: its index is the relative index of `H` in the range of `f`, which is finite.

Because the order of a subgroup divides the order of the group -- with the index as cofactor --
invertibility of the order of a finite group in a commutative semiring passes to every subgroup.
-/

public section

namespace Subgroup

/-- The preimage of a finite-index subgroup under a group homomorphism has finite index. -/
@[to_additive]
instance instFiniteIndexComap {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) [H.FiniteIndex]
    (f : G' →* G) : (H.comap f).FiniteIndex :=
  ⟨by rw [index_comap]; exact FiniteIndex.index_ne_zero⟩

end Subgroup

namespace TauCeti

/-- If the order of a finite group is invertible in `k`, then so is the order of any subgroup,
because the two differ by the index. -/
theorem isUnit_natCard_subgroup {k : Type*} {G : Type*} [CommSemiring k] [Group G] [Finite G]
    (S : Subgroup G) (hG : IsUnit (Nat.card G : k)) : IsUnit (Nat.card S : k) := by
  refine isUnit_of_mul_isUnit_left (y := (S.index : k)) ?_
  rwa [← Nat.cast_mul, S.card_mul_index]

end TauCeti
