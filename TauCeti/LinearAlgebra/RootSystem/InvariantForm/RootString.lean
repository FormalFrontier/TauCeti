/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# Invariant forms along root strings

This file records how an invariant bilinear form changes between consecutive roots in a root
string.  The results are the root-system calculation behind the integrality of Chevalley structure
constants.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
* R. W. Carter, *Simple Groups of Lie Type*, §4.1.

This advances the Chevalley-basis input to the explicit Chevalley--Demazure construction in Layer
9 of `TauCetiRoadmap/ReductiveGroups/README.md`, consumed by milestone L0 of the
`CFSGStatement` roadmap.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

namespace RootPairing

variable {I R M N : Type*} [Finite I] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing I R M N} [P.IsCrystallographic] [P.IsReduced]

/-- The lower endpoint of the root string through two roots is symmetric when their sum is a
root. -/
theorem chainBotCoeff_comm_of_root_add_mem {i j : I}
    (hadd : P.root i + P.root j ∈ range P.root) :
    P.chainBotCoeff i j = P.chainBotCoeff j i := by
  have hij := P.linearIndependent_of_add_mem_range_root' hadd
  have hji := P.linearIndependent_of_add_mem_range_root' (i := j) (j := i)
    (by simpa [add_comm] using hadd)
  have htop := P.one_le_chainTopCoeff_of_root_add_mem hadd
  have htop' := P.one_le_chainTopCoeff_of_root_add_mem (i := j) (j := i)
    (by simpa [add_comm] using hadd)
  have hlen := P.chainBotCoeff_add_chainTopCoeff_le_three (i := i) (j := j)
  have hlen' := P.chainBotCoeff_add_chainTopCoeff_le_three (i := j) (j := i)
  have hbot_le : P.chainBotCoeff i j ≤ 2 := by omega
  have htop_le : P.chainTopCoeff i j ≤ 3 := by omega
  have htop'_le : P.chainTopCoeff j i ≤ 3 := by omega
  have hbot : 1 ≤ P.chainBotCoeff i j ↔ 1 ≤ P.chainBotCoeff j i := by
    rw [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hij,
      ← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hji]
    simp only [one_smul]
    constructor
    · intro h
      have hn := (P.neg_mem_range_root_iff (x := P.root j - P.root i)).2 h
      simpa only [neg_sub] using hn
    · intro h
      have hn := (P.neg_mem_range_root_iff (x := P.root i - P.root j)).2 h
      simpa only [neg_sub] using hn
  have hpair := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  have hpq := P.chainBotCoeff_sub_chainTopCoeff hij
  have hpq' := P.chainBotCoeff_sub_chainTopCoeff hji
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hpair
  rcases hpair with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨h, h'⟩ <;> omega

namespace InvariantForm

/-- Two orthogonal roots whose sum is a root have the same squared length in every invariant
form. -/
theorem apply_root_self_eq_of_root_add_of_pairing_eq_zero (B : P.InvariantForm) {i j k : I}
    (hk : P.root k = P.root i + P.root j) (hij₀ : P.pairing i j = 0) :
    B.form (P.root i) (P.root i) = B.form (P.root j) (P.root j) := by
  -- Step 1: Establish orthogonality and compute pairings with the sum root k.
  have hadd : P.root i + P.root j ∈ range P.root := ⟨k, hk⟩
  have hlin := P.linearIndependent_of_add_mem_range_root' hadd
  have hji₀ : P.pairing j i = 0 := (P.pairing_eq_zero_iff' (i := i) (j := j)).mp hij₀
  have hki : P.pairing k i = 2 := by
    rw [← P.root_coroot'_eq_pairing, hk, map_add, P.root_coroot'_eq_pairing,
      P.root_coroot'_eq_pairing, hji₀, P.pairing_same, add_zero]
  have hkj : P.pairing k j = 2 := by
    rw [← P.root_coroot'_eq_pairing, hk, map_add, P.root_coroot'_eq_pairing,
      P.root_coroot'_eq_pairing, hij₀, P.pairing_same, zero_add]
  -- Step 2: Verify that i and j are distinct from ±k to apply the pairing classification.
  have hik : P.root i ≠ P.root k := by
    intro h
    have hj₀ : P.root j = 0 := by
      calc
        P.root j = (P.root i + P.root j) - P.root i := by abel
        _ = P.root k - P.root i := by rw [hk]
        _ = 0 := sub_eq_zero.mpr h.symm
    exact P.ne_zero j hj₀
  have hjk : P.root j ≠ P.root k := by
    intro h
    have hi₀ : P.root i = 0 := by
      calc
        P.root i = (P.root i + P.root j) - P.root j := by abel
        _ = P.root k - P.root j := by rw [hk]
        _ = 0 := sub_eq_zero.mpr h.symm
    exact P.ne_zero i hi₀
  have hik' : P.root i ≠ -P.root k := by
    intro h
    have hrel : (2 : R) • P.root i + (1 : R) • P.root j = 0 := by
      rw [one_smul, two_smul, add_assoc, ← hk, h, neg_add_cancel]
    exact one_ne_zero (hlin.eq_zero_of_pair hrel).2
  have hjk' : P.root j ≠ -P.root k := by
    intro h
    have hrel : (1 : R) • P.root i + (2 : R) • P.root j = 0 := by
      rw [one_smul, two_smul, ← add_assoc, ← hk, h, add_neg_cancel]
    exact one_ne_zero (hlin.eq_zero_of_pair hrel).1
  -- Step 3: Classify integer pairings `⟨i, k⟩` and `⟨j, k⟩` using `P.pairingIn_pairingIn_mem_set`.
  have hkiℤ : P.pairingIn ℤ k i = 2 := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    simpa only [P.algebraMap_pairingIn, map_ofNat] using hki
  have hkjℤ : P.pairingIn ℤ k j = 2 := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    simpa only [P.algebraMap_pairingIn, map_ofNat] using hkj
  have hpik := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i k
    hik hik'
  have hpjk := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' j k
    hjk hjk'
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hpik hpjk
  have hik₁ : P.pairing i k = 1 := by
    have : P.pairingIn ℤ i k = 1 := by omega
    rw [← P.algebraMap_pairingIn ℤ]
    rw [this]
    norm_num
  have hjk₁ : P.pairing j k = 1 := by
    have : P.pairingIn ℤ j k = 1 := by omega
    rw [← P.algebraMap_pairingIn ℤ]
    rw [this]
    norm_num
  -- Step 4: Combine the invariant-form swap identities `B(i, i) ⟨k, i⟩ = B(k, k) ⟨i, k⟩`.
  have hi := B.pairing_mul_eq_pairing_mul_swap i k
  have hj := B.pairing_mul_eq_pairing_mul_swap j k
  rw [hki, hik₁] at hi
  rw [hkj, hjk₁] at hj
  have htwo : (2 : R) ≠ 0 := by norm_num
  apply mul_left_cancel₀ htwo
  linear_combination hi - hj

/-- Along a root string, the squared lengths of two consecutive roots have the ratio of the
corresponding raising coefficients.  If `γ = α + β`, then

```text
q (γ, γ) = (p + 1) (β, β),
```

where `p = chainBotCoeff α β` and `q = chainTopCoeff α β`. -/
theorem chainTopCoeff_mul_apply_root_self_eq (B : P.InvariantForm) {i j k : I}
    (hk : P.root k = P.root i + P.root j) :
    (P.chainTopCoeff i j : R) * B.form (P.root k) (P.root k) =
      (P.chainBotCoeff i j + 1 : ℕ) * B.form (P.root j) (P.root j) := by
  -- Step 1: Linear independence and string endpoint bounds.
  have hadd : P.root i + P.root j ∈ range P.root := ⟨k, hk⟩
  have hij := P.linearIndependent_of_add_mem_range_root' hadd
  have hji := P.linearIndependent_of_add_mem_range_root' (i := j) (j := i)
    (by simpa [add_comm] using hadd)
  have hbot := chainBotCoeff_comm_of_root_add_mem (P := P) hadd
  have htop := P.one_le_chainTopCoeff_of_root_add_mem hadd
  have htop' := P.one_le_chainTopCoeff_of_root_add_mem (i := j) (j := i)
    (by simpa [add_comm] using hadd)
  have hlen := P.chainBotCoeff_add_chainTopCoeff_le_three (i := i) (j := j)
  have hlen' := P.chainBotCoeff_add_chainTopCoeff_le_three (i := j) (j := i)
  have hpq := P.chainBotCoeff_sub_chainTopCoeff hij
  have hpq' := P.chainBotCoeff_sub_chainTopCoeff hji
  -- Step 2: Distinctness of roots `i` and `±j` from linear independence.
  have hne : i ≠ j := by
    intro h
    subst j
    exact one_ne_zero (hij.eq_zero_of_pair' (s := 1) (t := 1) rfl).1
  have hne' : P.root i ≠ -P.root j := by
    intro h
    exact one_ne_zero (hij.eq_zero_of_pair' (s := 1) (t := -1) (by simpa using h)).1
  have hpair := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i j
    (fun h ↦ hne (P.root.injective h)) hne'
  -- Step 3: Bilinear expansion of `B(k, k) = B(i + j, i + j)` and invariant-form swap relation.
  have hsym : B.form (P.root j) (P.root i) = B.form (P.root i) (P.root j) := by
    simpa only [RingHom.id_apply] using B.symm.eq (P.root j) (P.root i)
  have hform :
      B.form (P.root k) (P.root k) =
        B.form (P.root i) (P.root i) + 2 * B.form (P.root i) (P.root j) +
          B.form (P.root j) (P.root j) := by
    rw [hk]
    simp only [map_add, LinearMap.add_apply]
    rw [hsym]
    ring
  have hcross :
      2 * B.form (P.root i) (P.root j) =
        P.pairing j i * B.form (P.root i) (P.root i) := by
    rw [← hsym]
    exact B.two_mul_apply_root_root j i
  have hpqR : P.pairing j i =
      (P.chainBotCoeff i j : R) - P.chainTopCoeff i j := by
    rw [← P.algebraMap_pairingIn ℤ, ← hpq]
    push_cast
    rfl
  have hpqR' : P.pairing i j =
      (P.chainBotCoeff j i : R) - P.chainTopCoeff j i := by
    rw [← P.algebraMap_pairingIn ℤ, ← hpq']
    push_cast
    rfl
  have hlength := B.pairing_mul_eq_pairing_mul_swap i j
  rw [hpqR, hpqR', ← hbot] at hlength
  rw [hform, hcross, hpqR]
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hpair
  -- Step 4: Case analysis on the root-pairing possibilities from the rank-2 classification.
  have hcases :
      P.chainTopCoeff i j = P.chainBotCoeff i j + 1 ∨
      (P.chainBotCoeff i j = 0 ∧ P.chainTopCoeff i j = 2 ∧
        P.chainTopCoeff j i = 1) ∨
      (P.chainBotCoeff i j = 0 ∧ P.chainTopCoeff i j = 3 ∧
        P.chainTopCoeff j i = 1) ∨
      (P.chainBotCoeff i j = 1 ∧ P.chainTopCoeff i j = 1 ∧
        P.chainTopCoeff j i = 1) ∨
      (P.chainBotCoeff i j = 2 ∧ P.chainTopCoeff i j = 1 ∧
        P.chainTopCoeff j i = 1) := by
    rcases hpair with h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨h, h'⟩ <;> omega
  rcases hcases with h | ⟨hp, hq, hq'⟩ | ⟨hp, hq, hq'⟩ |
      ⟨hp, hq, hq'⟩ | ⟨hp, hq, hq'⟩
  · rw [h]
    push_cast
    ring
  · norm_num [hp, hq, hq', hbot] at hlength ⊢
    rw [← hlength]
    ring
  · norm_num [hp, hq, hq', hbot] at hlength ⊢
    rw [← hlength]
    ring
  · have hij₀ : P.pairing i j = 0 := by
      rw [hpqR', ← hbot, hp, hq']
      norm_num
    have heq :=
      TauCeti.RootPairing.InvariantForm.apply_root_self_eq_of_root_add_of_pairing_eq_zero
        (P := P) B hk hij₀
    norm_num [hp, hq] at heq ⊢
    linear_combination heq
  · norm_num [hp, hq, hq', hbot] at hlength ⊢
    rw [hlength]
    ring

end InvariantForm

end RootPairing

end TauCeti
