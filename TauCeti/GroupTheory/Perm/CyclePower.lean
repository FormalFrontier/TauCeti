/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Powers of a cycle

A cycle `f` of a finite type has order the number `n = f.support.card` of points it moves
(`Equiv.Perm.IsCycle.orderOf`), and every power `f ^ k` again moves either all of those points or
none of them. This file computes the cycle type of such a power:

`(f ^ k).cycleType = Multiset.replicate d (n / d)` with `n = f.support.card` and `d = n.gcd k`,

so `f ^ k` splits into `gcd n k` cycles of the common length `n / gcd n k`. Mathlib computes the
order of a power (`orderOf_pow`) and decides when a power of a cycle is again a cycle
(`Equiv.Perm.IsCycle.pow_iff`) but does not compute the cycle type of one; the extra input is that
all the cycles of `f ^ k` have the *same* length, which holds because `(f ^ m) x = x` is
equivalent to `n ∣ m` independently of the point `x` of the support.

## Main results

* `TauCeti.pow_apply_eq_self_iff_of_isCycle`: `(f ^ k) x = x` holds for one point of the support
  exactly when it holds for all of them, namely exactly when `f.support.card ∣ k`.
* `TauCeti.cycleType_pow_of_isCycle`: the cycle type of `f ^ k` is `gcd n k` copies of
  `n / gcd n k`.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane
G.1 and Lane G.7: the component permutation of the standard grid diagram of the `(p, q)` torus
link is a power of the cyclic shift `finRotate`, and its cycle decomposition is what counts the
components of the represented link.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α] {f : Perm α}

/-- A power of a cycle fixes a point of its support exactly when the exponent is a multiple of the
length of the cycle, in which case the power is the identity.

The right-hand side does not mention `x`: such a power either moves every point of the support or
moves none of them. -/
theorem pow_apply_eq_self_iff_of_isCycle (hf : f.IsCycle) {x : α} (hx : x ∈ f.support) (k : ℕ) :
    (f ^ k) x = x ↔ f.support.card ∣ k := by
  rw [← hf.pow_eq_one_iff' (mem_support.mp hx), ← orderOf_dvd_iff_pow_eq_one, hf.orderOf]

/-- A power of a cycle moves every point of the support of that cycle, unless its exponent is a
multiple of the length of the cycle. -/
theorem pow_apply_ne_self_of_isCycle (hf : f.IsCycle) {k : ℕ} (hk : ¬f.support.card ∣ k) {x : α}
    (hx : x ∈ f.support) : (f ^ k) x ≠ x :=
  fun h => hk ((pow_apply_eq_self_iff_of_isCycle hf hx k).mp h)

/-- Every cycle of a power of a cycle of length `n` has the same length, namely the order
`n / gcd n k` of that power. -/
private theorem card_support_of_mem_cycleFactorsFinset_pow (hf : f.IsCycle) {k : ℕ} {c : Perm α}
    (hc : c ∈ (f ^ k).cycleFactorsFinset) :
    c.support.card = f.support.card / f.support.card.gcd k := by
  have horder : orderOf (f ^ k) = f.support.card / f.support.card.gcd k := by
    rw [orderOf_pow, hf.orderOf]
  have hcyc : c.IsCycle := (mem_cycleFactorsFinset_iff.mp hc).1
  obtain ⟨x, hx, -⟩ := id hcyc
  have hxf : x ∈ f.support :=
    support_pow_le f k (mem_cycleFactorsFinset_support_le hc (mem_support.mpr hx))
  have hcx : c = (f ^ k).cycleOf x := cycle_is_cycleOf (mem_support.mpr hx) hc
  rw [← hcyc.orderOf, ← horder]
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) (orderOf_dvd_of_pow_eq_one ?_)
  · -- `c` raised to the order of `f ^ k` fixes `x`, hence is the identity.
    refine (hcyc.pow_eq_one_iff' hx).mpr ?_
    rw [hcx, cycleOf_pow_apply_self, pow_orderOf_eq_one, one_apply]
  · -- conversely `f ^ k` raised to the order of `c` fixes `x`, hence is the identity.
    have hfix : (f ^ (k * orderOf c)) x = x := by
      rw [pow_mul, ← cycleOf_pow_apply_self, ← hcx, pow_orderOf_eq_one, one_apply]
    have hdvd : f.support.card ∣ k * orderOf c :=
      (pow_apply_eq_self_iff_of_isCycle hf hxf _).mp hfix
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rwa [hf.orderOf])

/-- The cycle type of a power of a cycle: writing `n = f.support.card` for the length of the
cycle, the permutation `f ^ k` is a product of `gcd n k` disjoint cycles, each of length
`n / gcd n k`.

The exponent is assumed not to be a multiple of `n`, which is exactly what rules out
`f ^ k = 1`. -/
theorem cycleType_pow_of_isCycle (hf : f.IsCycle) {k : ℕ} (hk : ¬f.support.card ∣ k) :
    (f ^ k).cycleType =
      Multiset.replicate (f.support.card.gcd k) (f.support.card / f.support.card.gcd k) := by
  have hn : 0 < f.support.card := by have := hf.two_le_card_support; omega
  have hd : 0 < f.support.card.gcd k := Nat.gcd_pos_of_pos_left _ hn
  have hdn : f.support.card.gcd k ∣ f.support.card := Nat.gcd_dvd_left _ _
  have hsupp : (f ^ k).support = f.support := hf.support_pow_eq_iff.mpr (by rwa [hf.orderOf])
  have hrep : (f ^ k).cycleType =
      Multiset.replicate (f ^ k).cycleType.card
        (f.support.card / f.support.card.gcd k) := by
    refine Multiset.eq_replicate.mpr ⟨rfl, fun m hm => ?_⟩
    rw [cycleType_def, Multiset.mem_map] at hm
    obtain ⟨c, hc, rfl⟩ := hm
    exact card_support_of_mem_cycleFactorsFinset_pow hf hc
  have hsum : (f ^ k).cycleType.card * (f.support.card / f.support.card.gcd k) =
      f.support.card := by
    have := (f ^ k).sum_cycleType
    rwa [hrep, Multiset.sum_replicate, smul_eq_mul, hsupp] at this
  have hcard : (f ^ k).cycleType.card = f.support.card.gcd k := by
    have hpos : 0 < f.support.card / f.support.card.gcd k :=
      Nat.div_pos (Nat.le_of_dvd hn hdn) hd
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hsum, Nat.mul_div_cancel' hdn]
  rw [hrep, hcard]

end TauCeti
