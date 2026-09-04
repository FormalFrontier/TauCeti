/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Normal subgroups with `p`-group quotient

Mathlib's `IsPGroup.to_quotient` says that every quotient of a `p`-group is again a `p`-group.
This file records the complementary behaviour, in which the group is fixed and the normal
subgroup varies: how the property `IsPGroup p (G ⧸ N)` of *the quotient* behaves under
intersection of normal subgroups and under preimage along a group homomorphism.

Both statements are group-theoretic, with no topology. They are what makes the family of
normal subgroups with `p`-group quotient usable: `IsPGroup.quotient_inf` says the family is
closed under binary intersection, hence downward directed, and `IsPGroup.quotient_comap` says
it is contravariantly functorial. The profinite development uses the first to run a compactness
argument on the family of open normal subgroups with `p`-group quotient, and the second to see
that a homomorphism into a pro-`p` group kills their intersection.

## Main results

* `IsPGroup.quotient_inf`: if `G ⧸ M` and `G ⧸ N` are `p`-groups, so is `G ⧸ (M ⊓ N)`.
* `IsPGroup.quotient_comap`: if `H ⧸ N` is a `p`-group and `f : G →* H`, then `G ⧸ N.comap f`
  is a `p`-group.
-/

public section

namespace TauCeti

variable {p : ℕ} {G : Type*} [Group G] {H : Type*} [Group H]

/-- If the quotients of `G` by two normal subgroups `M` and `N` are `p`-groups, then so is the
quotient by `M ⊓ N`: if `g ^ p ^ m` lies in `M` and `g ^ p ^ n` lies in `N`, then
`g ^ p ^ (m + n)`, which is a power of each of these, lies in both.

Consequently the normal subgroups of `G` with `p`-group quotient are closed under binary
intersection, hence downward directed. -/
theorem _root_.IsPGroup.quotient_inf {M N : Subgroup G} [M.Normal] [N.Normal]
    (hM : IsPGroup p (G ⧸ M)) (hN : IsPGroup p (G ⧸ N)) : IsPGroup p (G ⧸ M ⊓ N) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (M ⊓ N) x
  obtain ⟨m, hm⟩ := hM (QuotientGroup.mk' M g)
  obtain ⟨n, hn⟩ := hN (QuotientGroup.mk' N g)
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm hn
  refine ⟨m + n, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [pow_add, pow_mul]
    exact Subgroup.pow_mem M hm _
  · rw [pow_add, mul_comm, pow_mul]
    exact Subgroup.pow_mem N hn _

/-- If the quotient of `H` by a normal subgroup `N` is a `p`-group, then so is the quotient of
`G` by the preimage of `N` along any homomorphism `f : G →* H`: the induced map
`G ⧸ N.comap f →* H ⧸ N` is injective, because `N.comap f` consists of exactly the elements
that `f` sends into `N`. -/
theorem _root_.IsPGroup.quotient_comap {N : Subgroup H} [N.Normal] (hN : IsPGroup p (H ⧸ N))
    (f : G →* H) : IsPGroup p (G ⧸ N.comap f) := by
  refine hN.of_injective (QuotientGroup.map (N.comap f) N f le_rfl) ?_
  intro a b hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.comap f) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N.comap f) b
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.map_mk,
    QuotientGroup.map_mk, QuotientGroup.eq] at hab
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  simpa using hab

end TauCeti
