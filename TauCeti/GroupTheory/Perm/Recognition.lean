/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Recognizing cycles and transpositions in a permutation group

This file supplies permutation-group recognition steps used to recognize full symmetric groups
from cycle data. A transitive subgroup of a finite symmetric group whose degree is prime contains
a full cycle: the proof combines orbit--stabilizer with Cauchy's theorem and the permutation-group
criterion that an element of prime order in prime degree is a cycle. A permutation with exactly
one 2-cycle and only odd-length remaining cycles has an explicit odd power that is a
transposition: the product of the odd lengths kills every remaining cycle while preserving the
2-cycle.

## Main results

* `TauCeti.exists_isCycle_mem_of_isPretransitive_of_prime_card`: a transitive permutation group
  of prime degree contains a full cycle.
* `Equiv.Perm.isSwap_pow_prod_erase_two_cycleType_and_odd`: if a permutation has exactly one
  2-cycle and all its other cycles have odd length, an explicit odd power is a transposition.
* `Equiv.Perm.exists_odd_isSwap_pow`: the corresponding existential form.

## References

* `TauCetiRoadmap/PolynomialGaloisGroups/README.md`, which specifies both recognition steps: the
  full cycle in a transitive group of prime degree, and the odd power of a permutation with a
  unique 2-cycle and otherwise odd cycle lengths that is a transposition.
-/

public section

namespace TauCeti

open MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A transitive permutation group of prime degree contains a full cycle.

The returned permutation has order and support cardinality equal to the degree, so its support
is all of `α`. This is intended as a prime-degree recognition input for the low-degree
classification and for the prime-degree branch of the `Sₙ` realization argument.
-/
theorem exists_isCycle_mem_of_isPretransitive_of_prime_card
    {G : Subgroup (Equiv.Perm α)} (hG : IsPretransitive G α)
    (hp : Nat.Prime (Fintype.card α)) :
    ∃ g : Equiv.Perm α, g ∈ G ∧ g.IsCycle ∧ g.support = Finset.univ := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let a : α := Classical.choice (Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hp.ne_zero))
  have horbit : orbit G a = Set.univ :=
    (isPretransitive_iff_orbit_eq_univ a).mp hG
  have hcard : Fintype.card α ∣ Fintype.card G := by
    refine ⟨Fintype.card (stabilizer G a), ?_⟩
    simpa [horbit, Nat.mul_comm] using
      (card_orbit_mul_card_stabilizer_eq_card_group (G := G) a).symm
  let _ : Fact (Fintype.card α).Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) hcard
  have horder : orderOf (g : Equiv.Perm α) = Fintype.card α :=
    (Subgroup.orderOf_coe g).trans hg
  have hcycle : (g : Equiv.Perm α).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order'' hp horder
  have hsupport : (g : Equiv.Perm α).support = Finset.univ :=
    Finset.eq_univ_of_card (g : Equiv.Perm α).support (hcycle.orderOf.symm.trans horder)
  exact ⟨g, g.property, hcycle, hsupport⟩

/-- If a permutation has exactly one cycle of length two and every other cycle has odd length,
then raising it to the product of those other cycle lengths gives a transposition.

The exponent is itself odd. This is the cycle-theoretic step used to turn a factorization pattern
with one quadratic factor and only odd-degree remaining factors into a transposition in a Galois
group. -/
theorem _root_.Equiv.Perm.isSwap_pow_prod_erase_two_cycleType_and_odd {σ : Equiv.Perm α}
    (htwo : σ.cycleType.count 2 = 1)
    (hodd : ∀ n ∈ σ.cycleType, n ≠ 2 → Odd n) :
    (σ ^ (σ.cycleType.erase 2).prod).IsSwap ∧ Odd (σ.cycleType.erase 2).prod := by
  have hmem : 2 ∈ σ.cycleType := Multiset.count_pos.mp (by omega)
  obtain ⟨c, τ, hσ, hdisj, hc, hcard⟩ := Equiv.Perm.mem_cycleType_iff.mp hmem
  have hcSwap : c.IsSwap := Equiv.Perm.card_support_eq_two.mp hcard
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
  have hkodd : Odd τ.cycleType.prod :=
    Multiset.prod_induction Odd τ.cycleType (fun _ _ ha hb ↦ ha.mul hb) (by simp) hoddτ
  have hτpow : τ ^ τ.cycleType.prod = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType]
    exact Multiset.lcm_dvd.mpr fun _ hn ↦ Multiset.dvd_prod hn
  have hcpow : c ^ τ.cycleType.prod = c := by
    have hmod : τ.cycleType.prod ≡ 1 [MOD orderOf c] := by
      rw [hcSwap.orderOf, Nat.ModEq, Nat.odd_iff.mp hkodd]
    exact ((pow_eq_pow_iff_modEq).mpr hmod).trans (pow_one c)
  rw [herase, hσ, hdisj.commute.mul_pow, hcpow, hτpow, mul_one]
  exact ⟨hcSwap, hkodd⟩

/-- A permutation with exactly one 2-cycle and all remaining cycle lengths odd has an odd power
that is a transposition. -/
theorem _root_.Equiv.Perm.exists_odd_isSwap_pow {σ : Equiv.Perm α}
    (htwo : σ.cycleType.count 2 = 1)
    (hodd : ∀ n ∈ σ.cycleType, n ≠ 2 → Odd n) :
    ∃ k, Odd k ∧ (σ ^ k).IsSwap := by
  have h := σ.isSwap_pow_prod_erase_two_cycleType_and_odd htwo hodd
  exact ⟨(σ.cycleType.erase 2).prod, h.2, h.1⟩

end TauCeti
