/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Character
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Primes with prescribed prime-discriminant characters

Let `P₁, …, P_t` be distinct prime discriminants, at most one of them even, and let a sign
`ε_i = ±1` be assigned to each. Then there are infinitely many primes `q` at which the characters
attached to the `P_i` take exactly the prescribed values, `χ_{P_i}(q) = ε_i` for every `i`. This is
the arithmetic input that makes the genus characters of a quadratic field *independent*: the lower
bound `t - 1` on the `2`-rank of the narrow class group of `ℚ(√d)` comes from realising every sign
pattern of product `1` by the class of a prime ideal of degree one, and this file supplies the
rational prime under that ideal.

Three facts combine. Each character `χ_P` is nontrivial, so it takes the value `-1` somewhere; the
moduli `|P_i|` of distinct prime discriminants are pairwise coprime, so the Chinese remainder
theorem produces one residue class with all the prescribed values at once; and Dirichlet's theorem
on primes in arithmetic progressions (`Nat.forall_exists_prime_gt_and_zmodEq`) places a prime,
larger than any given bound, in that class.

The statement is classical; see D. A. Cox, *Primes of the Form x² + ny²*, §3.B (the proof of
Theorem 3.15), and F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.

The nontriviality of a single character (`exists_primeDiscriminantCharFun_eq`) and the coprimality
of distinct prime discriminants (`isCoprime_primeDiscriminant_of_ne_of_not_both_even`) are
supplied by `TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Character` and
`TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants`.

## Main results

* `TauCeti.Multiquadratic.exists_forall_primeDiscriminantCharFun_eq`: a natural number at which
  finitely many prime-discriminant characters take prescribed values.
* `TauCeti.Multiquadratic.exists_prime_gt_forall_primeDiscriminantCharFun_eq`: an odd prime,
  larger than any given bound, at which they take prescribed values.
-/

public section

namespace TauCeti.Multiquadratic

/-! ### Prescribing several characters at once -/

/-- **Prescribing the characters of finitely many prime discriminants.** Let `s` be a finite set
of prime discriminants, at most one of them even, and let `ε` assign a sign to each. Then some
natural number `a` has `χ_P(a) = ε P` for every `P ∈ s`. -/
theorem exists_forall_primeDiscriminantCharFun_eq {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q)
    (ε : ℤ → ℤˣ) :
    ∃ a : ℕ, ∀ P ∈ s, primeDiscriminantCharFun P a = ε P := by
  classical
  choose! r hr using fun P (hP : P ∈ s) => exists_primeDiscriminantCharFun_eq (hs P hP) (ε P)
  have hmod : ∀ P ∈ s, P.natAbs ≠ 0 := fun P hP =>
    Int.natAbs_ne_zero.mpr (hs P hP).ne_zero
  have hcop : Set.Pairwise (↑s : Set ℤ) (Function.onFun Nat.Coprime fun P : ℤ => P.natAbs) :=
    fun P hP Q hQ hne => Int.isCoprime_iff_nat_coprime.mp
      (isCoprime_primeDiscriminant_of_ne_of_not_both_even (hs P hP) (hs Q hQ) hne
        fun h => hne (heven P hP Q hQ h.1 h.2))
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset r (fun P : ℤ => P.natAbs) s hmod hcop
  refine ⟨a, fun P hP => ?_⟩
  rw [← hr P hP]
  apply primeDiscriminantCharFun_mod_right'
  have h := ha P hP
  unfold Nat.ModEq at h
  exact_mod_cast h

/-- **Dirichlet's theorem for prime-discriminant characters.** Let `s` be a finite set of prime
discriminants, at most one of them even, let `ε` assign a sign to each, and let `N` be any bound.
Then some odd prime `q > N` has `χ_P(q) = ε P` for every `P ∈ s`. In particular there are
infinitely many such primes. -/
theorem exists_prime_gt_forall_primeDiscriminantCharFun_eq {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q)
    (ε : ℤ → ℤˣ) (N : ℕ) :
    ∃ q : ℕ, N < q ∧ q.Prime ∧ q ≠ 2 ∧ ∀ P ∈ s, primeDiscriminantCharFun P q = ε P := by
  classical
  obtain ⟨a, ha⟩ := exists_forall_primeDiscriminantCharFun_eq hs heven ε
  have hM0 : (∏ P ∈ s, P.natAbs) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P hP =>
    Int.natAbs_ne_zero.mpr (hs P hP).ne_zero
  have hcop : IsCoprime (a : ℤ) ((∏ P ∈ s, P.natAbs : ℕ) : ℤ) := by
    rw [Nat.cast_prod]
    refine IsCoprime.prod_right fun P hP => ?_
    have h1 : IsCoprime (a : ℤ) P := by
      by_contra h
      have h0 := (primeDiscriminantCharFun_eq_zero_iff (hs P hP)).mpr h
      rw [ha P hP] at h0
      exact (ε P).ne_zero h0
    rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
    exact Int.isCoprime_iff_nat_coprime.mp h1
  obtain ⟨q, hqN, hq, hqa⟩ := Nat.forall_exists_prime_gt_and_zmodEq (max N 2) hM0 hcop
  refine ⟨q, lt_of_le_of_lt (le_max_left _ _) hqN, hq, ?_, fun P hP => ?_⟩
  · have := lt_of_le_of_lt (le_max_right _ _) hqN
    omega
  · rw [← ha P hP]
    apply primeDiscriminantCharFun_mod_right'
    have hdvd : ((P.natAbs : ℕ) : ℤ) ∣ ((∏ P ∈ s, P.natAbs : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem _ hP)
    exact hqa.of_dvd hdvd

end TauCeti.Multiquadratic
