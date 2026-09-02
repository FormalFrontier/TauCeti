/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup

/-!
# Quotients of a group that are `p`-groups

Mathlib's `IsPGroup.to_quotient` says that a quotient of a `p`-group is a `p`-group. This file
records the two complementary stability properties of the *family* of normal subgroups with
`p`-group quotient: it is closed under intersection, and it pulls back along homomorphisms.

Together these say that the normal subgroups with `p`-group quotient form a filter base that is
natural in the group, which is what makes the pro-`p` kernel of
`TauCeti/Topology/Algebra/Group/Profinite/MaximalProPQuotient.lean` a downward-directed
intersection.

## Main results

* `IsPGroup.quotient_inf`: the quotient by an intersection of two normal subgroups with
  `p`-group quotient is a `p`-group.
* `IsPGroup.quotient_comap`: the quotient by the preimage of a normal subgroup with `p`-group
  quotient is a `p`-group.
-/

public section

universe u v

variable {p : ℕ}

/-- If the quotients of `G` by two normal subgroups are `p`-groups, then so is the quotient by
their intersection. -/
theorem IsPGroup.quotient_inf {G : Type u} [Group G] {U V : Subgroup G} [U.Normal] [V.Normal]
    (hU : IsPGroup p (G ⧸ U)) (hV : IsPGroup p (G ⧸ V)) : IsPGroup p (G ⧸ (U ⊓ V)) := by
  -- An element killed by `p ^ k` in `G ⧸ U` and by `p ^ l` in `G ⧸ V` is killed by `p ^ (k + l)`
  -- in both, hence in `G ⧸ (U ⊓ V)`.
  have key : ∀ (W : Subgroup G) [W.Normal] (a : G) (n : ℕ), (a : G ⧸ W) ^ n = 1 ↔ a ^ n ∈ W := by
    intro W _ a n
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  rw [isPGroup_iff_pow_pow_eq_one] at hU hV ⊢
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, hk⟩ := hU a
  obtain ⟨l, hl⟩ := hV a
  rw [key] at hk hl
  refine ⟨k + l, ?_⟩
  rw [key]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [pow_add, pow_mul]
    exact Subgroup.pow_mem _ hk _
  · rw [pow_add, mul_comm, pow_mul]
    exact Subgroup.pow_mem _ hl _

/-- The quotient of `G` by the preimage of a normal subgroup `V` of `H` under a homomorphism
`f : G →* H` is a `p`-group as soon as `H ⧸ V` is, since it embeds into `H ⧸ V`. -/
theorem IsPGroup.quotient_comap {G : Type u} {H : Type v} [Group G] [Group H] {V : Subgroup H}
    [V.Normal] (hV : IsPGroup p (H ⧸ V)) (f : G →* H) : IsPGroup p (G ⧸ V.comap f) := by
  rw [isPGroup_iff_pow_pow_eq_one] at hV ⊢
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, hk⟩ := hV (f a)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_comap, map_pow]
  exact hk
