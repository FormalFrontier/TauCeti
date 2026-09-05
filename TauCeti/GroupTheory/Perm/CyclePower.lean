/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Powers and cycle decompositions of permutations

A cycle `f` of a finite type has order the number `n = f.support.card` of points it moves
(`Equiv.Perm.IsCycle.orderOf`), and every power `f ^ k` again moves either all of those points or
none of them. This file computes the cycle type of such a power: whenever `n ∤ k` (equivalently,
whenever `f ^ k ≠ 1`),

`(f ^ k).cycleType = Multiset.replicate d (n / d)` with `n = f.support.card` and `d = n.gcd k`,

so a nonidentity power `f ^ k` splits into `gcd n k` cycles of the common length `n / gcd n k`;
for `n ∣ k` the power is the identity and its cycle type is empty. Mathlib computes the
order of a power (`orderOf_pow`) and decides when a power of a cycle is again a cycle
(`Equiv.Perm.IsCycle.pow_iff`) but does not compute the cycle type of one; the extra input is that
all the cycles of `f ^ k` have the *same* length, which holds because `(f ^ m) x = x` is
equivalent to `orderOf f ∣ m` independently of the point `x` of the support.

The final results apply this power calculus to a general permutation with one 2-cycle and only
odd-length remaining cycles. The product of the odd lengths kills every remaining cycle while
preserving the 2-cycle, so it is an explicit odd exponent whose power is a transposition.

## Main results

* `Equiv.Perm.IsCycle.pow_apply_eq_self_iff`: `(f ^ n) x = x` holds for one point moved by the
  cycle exactly when it holds for all of them, namely exactly when `orderOf f ∣ n`.
* `Equiv.Perm.IsCycle.cycleType_pow_of_not_dvd`: for `n ∤ k`, the cycle type of `f ^ k` is
  `gcd n k` copies of `n / gcd n k`.
* `Equiv.Perm.isSwap_pow_prod_erase_two_cycleType_and_odd`: if a permutation has exactly one
  2-cycle and all its other cycles have odd length, an explicit odd power is a transposition.
* `Equiv.Perm.exists_odd_isSwap_pow`: the corresponding existential form.

The cycle-specific declarations are stated in the `Equiv.Perm.IsCycle` namespace, giving dot
notation from `hf : f.IsCycle`. The recognition declarations are in `Equiv.Perm`, giving dot
notation from the permutation itself.

## References

* [Mathlib PR #42723](https://github.com/leanprover-community/mathlib4/pull/42723)
  (Kim Morrison) — the draft upstream adaptation of this file; the `Equiv.Perm.IsCycle`
  namespace, the `orderOf`-based statement of the fixed-point lemma, and the dropped
  support-card wrapper all follow the form prepared for that PR.

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane
G.1 and Lane G.7: the component permutation of the standard grid diagram of the `(p, q)` torus
link is a power of the cyclic shift `finRotate`, and its cycle decomposition is what counts the
components of the represented link.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

/-- A power of a cycle fixes a point moved by the cycle exactly when the exponent is a multiple
of the order of the cycle. Since the right-hand side does not depend on the point, a power of a
cycle either moves every point the cycle moves, or fixes all of them. -/
@[simp]
theorem _root_.Equiv.Perm.IsCycle.pow_apply_eq_self_iff {β : Type*} [Finite β] {f : Perm β}
    (hf : f.IsCycle) {n : ℕ} {x : β} (hx : f x ≠ x) : (f ^ n) x = x ↔ orderOf f ∣ n := by
  rw [← hf.pow_eq_one_iff' hx, orderOf_dvd_iff_pow_eq_one]

variable {α : Type*} [DecidableEq α] [Fintype α] {f : Perm α}

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
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp ((hf.pow_apply_eq_self_iff (mem_support.mp hxf)).mp hfix)

/-- The cycle type of a power of a cycle: writing `n = f.support.card` for the length of the
cycle, the permutation `f ^ k` is a product of `gcd n k` disjoint cycles, each of length
`n / gcd n k`.

The exponent is assumed not to be a multiple of `n`, which is exactly what rules out
`f ^ k = 1`. -/
theorem _root_.Equiv.Perm.IsCycle.cycleType_pow_of_not_dvd (hf : f.IsCycle) {k : ℕ}
    (hk : ¬f.support.card ∣ k) : (f ^ k).cycleType =
      Multiset.replicate (f.support.card.gcd k) (f.support.card / f.support.card.gcd k) := by
  have hn : 0 < f.support.card := zero_lt_two.trans_le hf.two_le_card_support
  have hd : f.support.card.gcd k ∣ f.support.card := Nat.gcd_dvd_left _ _
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
      Nat.div_pos (Nat.le_of_dvd hn hd) (Nat.gcd_pos_of_pos_left k hn)
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hsum, Nat.mul_div_cancel' hd]
  rw [hrep, hcard]

/-- If a permutation has exactly one cycle of length two and every other cycle has odd length,
then raising it to the product of those other cycle lengths gives a transposition.

The exponent is itself odd. This is the cycle-theoretic step used to turn a factorization pattern
with one quadratic factor and only odd-degree remaining factors into a transposition in a Galois
group. -/
theorem _root_.Equiv.Perm.isSwap_pow_prod_erase_two_cycleType_and_odd {σ : Perm α}
    (htwo : σ.cycleType.count 2 = 1)
    (hodd : ∀ n ∈ σ.cycleType, n ≠ 2 → Odd n) :
    (σ ^ (σ.cycleType.erase 2).prod).IsSwap ∧ Odd (σ.cycleType.erase 2).prod := by
  have hmem : 2 ∈ σ.cycleType := Multiset.count_pos.mp (by omega)
  obtain ⟨c, τ, hσ, hdisj, hc, hcard⟩ := mem_cycleType_iff.mp hmem
  have hcSwap : c.IsSwap := card_support_eq_two.mp hcard
  have hcycleType : σ.cycleType = {2} + τ.cycleType := by
    rw [hσ, hdisj.cycleType_mul, hc.cycleType, hcard]
  have herase : σ.cycleType.erase 2 = τ.cycleType := by
    rw [hcycleType]
    simp
  have htwoτ : 2 ∉ τ.cycleType := by
    rw [← Multiset.count_eq_zero]
    have : 1 + τ.cycleType.count 2 = 1 := by
      simpa [hcycleType] using htwo
    omega
  have hoddτ : ∀ n ∈ τ.cycleType, Odd n := by
    intro n hn
    have hnσ : n ∈ σ.cycleType := by
      rw [hcycleType, Multiset.mem_add]
      exact Or.inr hn
    exact (hodd n hnσ) (fun hn2 ↦ htwoτ (hn2 ▸ hn))
  have odd_prod : ∀ s : Multiset ℕ, (∀ n ∈ s, Odd n) → Odd s.prod := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons n s ih =>
        rw [Multiset.prod_cons]
        exact (hs n (by simp)).mul (ih fun m hm ↦ hs m (by simp [hm]))
  have hkodd : Odd τ.cycleType.prod := odd_prod τ.cycleType hoddτ
  have hτpow : τ ^ τ.cycleType.prod = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← lcm_cycleType]
    exact Multiset.lcm_dvd.mpr fun _ hn ↦ Multiset.dvd_prod hn
  have hcpow : c ^ τ.cycleType.prod = c := by
    have hmod : τ.cycleType.prod ≡ 1 [MOD orderOf c] := by
      rw [hcSwap.orderOf, Nat.ModEq, Nat.odd_iff.mp hkodd]
    exact ((pow_eq_pow_iff_modEq).mpr hmod).trans (pow_one c)
  rw [herase, hσ, hdisj.commute.mul_pow, hcpow, hτpow, mul_one]
  exact ⟨hcSwap, hkodd⟩

/-- A permutation with exactly one 2-cycle and all remaining cycle lengths odd has an odd power
that is a transposition. -/
theorem _root_.Equiv.Perm.exists_odd_isSwap_pow {σ : Perm α}
    (htwo : σ.cycleType.count 2 = 1)
    (hodd : ∀ n ∈ σ.cycleType, n ≠ 2 → Odd n) :
    ∃ k, Odd k ∧ (σ ^ k).IsSwap := by
  have h := σ.isSwap_pow_prod_erase_two_cycleType_and_odd htwo hodd
  exact ⟨(σ.cycleType.erase 2).prod, h.2, h.1⟩

end TauCeti
