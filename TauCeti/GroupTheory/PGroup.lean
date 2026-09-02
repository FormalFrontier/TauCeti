/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup

/-!
# Products of `p`-groups

Mathlib's `IsPGroup` is stable under subgroups, quotients, images and preimages along injective
maps. This file adds the remaining elementary closure property, stability under a product over
a finite index type: given elements of finite `p`-power order in each factor, a common exponent
is obtained by taking the supremum of the individual ones.

Note that the exponent computation `Monoid.exponent_pi` does not give this: a `p`-group need
not have finite exponent, and the argument here needs no such bound.

## Main results

* `IsPGroup.pi`: a product of finitely many `p`-groups is a `p`-group.
-/

public section

namespace TauCeti

/-- A product of finitely many `p`-groups is a `p`-group. -/
theorem _root_.IsPGroup.pi {p : ℕ} {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    (h : ∀ i, IsPGroup p (G i)) : IsPGroup p (∀ i, G i) := by
  classical
  have := Fintype.ofFinite ι
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  choose k hk using fun i ↦ isPGroup_iff_pow_pow_eq_one.mp (h i) (g i)
  refine ⟨Finset.univ.sup k, funext fun i ↦ ?_⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := k) (Finset.mem_univ i))
  rw [Pi.pow_apply, Pi.one_apply, hm, pow_add, pow_mul, hk i, one_pow]

end TauCeti
