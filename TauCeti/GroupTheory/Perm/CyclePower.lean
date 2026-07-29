/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Powers of a cyclic permutation of the whole type

A permutation `f` of a finite type `α` which is a cycle moving every point — that is, a cycle
whose support is all of `α` — has order `Fintype.card α`, and every power `f ^ k` again moves
either every point or none. This file computes the cycle type of such a power:

`(f ^ k).cycleType = Multiset.replicate d (n / d)` with `n = Fintype.card α` and `d = n.gcd k`,

so `f ^ k` splits into `gcd n k` cycles of the common length `n / gcd n k`, and in particular is
itself a cycle exactly when `n` and `k` are coprime. Mathlib computes the order of a power
(`orderOf_pow`) but not the cycle type of one; the extra input is that all the cycles of `f ^ k`
have the *same* length, which holds here because `(f ^ m) x = x` is equivalent to `n ∣ m`
independently of `x`.

## Main results

* `TauCeti.pow_apply_eq_self_iff_of_isCycle`: `(f ^ k) x = x` holds for one point exactly when it
  holds for all of them, namely exactly when `Fintype.card α ∣ k`.
* `TauCeti.cycleType_pow_of_isCycle`: the cycle type of `f ^ k` is `gcd n k` copies of
  `n / gcd n k`.
* `TauCeti.isCycle_pow_iff_of_isCycle`: `f ^ k` is a cycle exactly when `n` and `k` are coprime.

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

/-- A cycle moving every point of a finite type has order the cardinality of the type. -/
theorem orderOf_eq_card_of_isCycle (hf : f.IsCycle) (hsupp : f.support = Finset.univ) :
    orderOf f = Fintype.card α := by
  rw [hf.orderOf, hsupp, Finset.card_univ]

/-- A power of a cycle moving every point of a finite type fixes one point exactly when the
exponent is a multiple of the cardinality, in which case the power is the identity.

The right-hand side does not mention `x`: such a power either moves every point or moves none. -/
theorem pow_apply_eq_self_iff_of_isCycle (hf : f.IsCycle) (hsupp : f.support = Finset.univ)
    (k : ℕ) (x : α) : (f ^ k) x = x ↔ Fintype.card α ∣ k := by
  have hx : f x ≠ x := mem_support.mp (hsupp ▸ Finset.mem_univ x)
  rw [← hf.pow_eq_one_iff' hx, ← orderOf_dvd_iff_pow_eq_one,
    orderOf_eq_card_of_isCycle hf hsupp]

/-- A power of a cycle moving every point of a finite type moves every point, unless its exponent
is a multiple of the cardinality. -/
theorem pow_apply_ne_self_of_isCycle (hf : f.IsCycle) (hsupp : f.support = Finset.univ)
    {k : ℕ} (hk : ¬Fintype.card α ∣ k) (x : α) : (f ^ k) x ≠ x :=
  fun h => hk ((pow_apply_eq_self_iff_of_isCycle hf hsupp k x).mp h)

/-- A power of a cycle moving every point of a finite type again moves every point, unless its
exponent is a multiple of the cardinality. -/
theorem support_pow_of_isCycle (hf : f.IsCycle) (hsupp : f.support = Finset.univ)
    {k : ℕ} (hk : ¬Fintype.card α ∣ k) : (f ^ k).support = Finset.univ := by
  ext x
  simpa using pow_apply_ne_self_of_isCycle hf hsupp hk x

/-- Every cycle of a power of a cycle moving every point of a finite type has the same length,
namely the order `n / gcd n k` of that power. -/
theorem card_support_of_mem_cycleFactorsFinset_pow (hf : f.IsCycle)
    (hsupp : f.support = Finset.univ) {k : ℕ} {c : Perm α}
    (hc : c ∈ (f ^ k).cycleFactorsFinset) :
    c.support.card = Fintype.card α / (Fintype.card α).gcd k := by
  have horder : orderOf (f ^ k) = Fintype.card α / (Fintype.card α).gcd k := by
    rw [orderOf_pow, orderOf_eq_card_of_isCycle hf hsupp]
  have hcyc : c.IsCycle := (mem_cycleFactorsFinset_iff.mp hc).1
  obtain ⟨x, hx, -⟩ := id hcyc
  have hcx : c = (f ^ k).cycleOf x := cycle_is_cycleOf (mem_support.mpr hx) hc
  rw [← hcyc.orderOf, ← horder]
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) (orderOf_dvd_of_pow_eq_one ?_)
  · -- `c` raised to the order of `f ^ k` fixes `x`, hence is the identity.
    refine (hcyc.pow_eq_one_iff' hx).mpr ?_
    rw [hcx, cycleOf_pow_apply_self, pow_orderOf_eq_one, one_apply]
  · -- conversely `f ^ k` raised to the order of `c` fixes `x`, hence is the identity.
    have hfix : (f ^ (k * orderOf c)) x = x := by
      rw [pow_mul, ← cycleOf_pow_apply_self, ← hcx, pow_orderOf_eq_one, one_apply]
    have hdvd : Fintype.card α ∣ k * orderOf c :=
      (pow_apply_eq_self_iff_of_isCycle hf hsupp _ x).mp hfix
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp
      (by rwa [orderOf_eq_card_of_isCycle hf hsupp])

/-- The cycle type of a power of a cycle moving every point of a finite type: writing
`n = Fintype.card α`, the permutation `f ^ k` is a product of `gcd n k` disjoint cycles, each of
length `n / gcd n k`.

The exponent is assumed not to be a multiple of `n`, which is exactly what rules out
`f ^ k = 1`. -/
theorem cycleType_pow_of_isCycle (hf : f.IsCycle) (hsupp : f.support = Finset.univ)
    {k : ℕ} (hk : ¬Fintype.card α ∣ k) :
    (f ^ k).cycleType =
      Multiset.replicate ((Fintype.card α).gcd k)
        (Fintype.card α / (Fintype.card α).gcd k) := by
  obtain ⟨y, -, -⟩ := id hf
  have hn : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨y⟩
  have hd : 0 < (Fintype.card α).gcd k := Nat.gcd_pos_of_pos_left _ hn
  have hdn : (Fintype.card α).gcd k ∣ Fintype.card α := Nat.gcd_dvd_left _ _
  have hrep : (f ^ k).cycleType =
      Multiset.replicate (f ^ k).cycleType.card
        (Fintype.card α / (Fintype.card α).gcd k) := by
    refine Multiset.eq_replicate.mpr ⟨rfl, fun m hm => ?_⟩
    rw [cycleType_def, Multiset.mem_map] at hm
    obtain ⟨c, hc, rfl⟩ := hm
    exact card_support_of_mem_cycleFactorsFinset_pow hf hsupp hc
  have hsum : (f ^ k).cycleType.card * (Fintype.card α / (Fintype.card α).gcd k) =
      Fintype.card α := by
    have := (f ^ k).sum_cycleType
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, support_pow_of_isCycle hf hsupp hk,
      Finset.card_univ] at this
    exact this
  have hcard : (f ^ k).cycleType.card = (Fintype.card α).gcd k := by
    have hpos : 0 < Fintype.card α / (Fintype.card α).gcd k :=
      Nat.div_pos (Nat.le_of_dvd hn hdn) hd
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hsum, Nat.mul_div_cancel' hdn]
  rw [hrep, hcard]

/-- A power of a cycle moving every point of a finite type is again a cycle exactly when the
exponent is coprime to the cardinality of the type. -/
theorem isCycle_pow_iff_of_isCycle (hf : f.IsCycle) (hsupp : f.support = Finset.univ)
    {k : ℕ} (hk : ¬Fintype.card α ∣ k) :
    (f ^ k).IsCycle ↔ (Fintype.card α).Coprime k := by
  rw [← card_cycleType_eq_one, cycleType_pow_of_isCycle hf hsupp hk, Multiset.card_replicate,
    Nat.Coprime]

end TauCeti
