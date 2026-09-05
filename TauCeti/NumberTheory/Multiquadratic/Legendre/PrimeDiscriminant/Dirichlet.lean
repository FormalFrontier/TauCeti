/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Character
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.FieldTheory.Finite.Basic
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

## Main results

* `TauCeti.Multiquadratic.exists_primeDiscriminantCharFun_eq_neg_one` and
  `TauCeti.Multiquadratic.exists_primeDiscriminantCharFun_eq`: the character attached to a prime
  discriminant is nontrivial, so it takes each of the values `±1` at some natural number.
* `TauCeti.Multiquadratic.natAbs_coprime_natAbs_of_ne`: the moduli of two distinct prime
  discriminants are coprime, provided they are not two distinct even prime discriminants.
* `TauCeti.Multiquadratic.exists_forall_primeDiscriminantCharFun_eq`: a natural number at which
  finitely many prime-discriminant characters take prescribed values.
* `TauCeti.Multiquadratic.exists_prime_gt_forall_primeDiscriminantCharFun_eq`: an odd prime,
  larger than any given bound, at which they take prescribed values.
-/

public section

namespace TauCeti.Multiquadratic

/-! ### Nontriviality of a single character -/

/-- **The character of a prime discriminant is nontrivial.** For every prime discriminant `P`,
some natural number has character `-1` at `P`: the residue `3` for the even prime discriminants
`-4` and `8`, the residue `5` for `-8`, and any quadratic non-residue modulo `p` for `p* = ±p`. -/
theorem exists_primeDiscriminantCharFun_eq_neg_one {P : ℤ} (hP : IsPrimeDiscriminant P) :
    ∃ a : ℕ, primeDiscriminantCharFun P a = -1 := by
  rcases isPrimeDiscriminant_iff.mp hP with hev | ⟨p, hp, hodd, rfl⟩
  · rcases hev with rfl | rfl | rfl
    · exact ⟨3, by rw [primeDiscriminantCharFun_neg_four]; exact ZMod.χ₄_int_three_mod_four rfl⟩
    · exact ⟨3, by rw [primeDiscriminantCharFun_eight, ZMod.χ₈_int_eq_if_mod_eight]; norm_num⟩
    · exact ⟨5, by
        rw [primeDiscriminantCharFun_neg_eight, ZMod.χ₈'_int_eq_if_mod_eight]; norm_num⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by have := Nat.odd_iff.mp hodd; omega
    have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare hchar
    refine ⟨x.val, ?_⟩
    rw [primeDiscriminantCharFun_oddPrimeDiscriminant hodd, ← jacobiSym.legendreSym.to_jacobiSym,
      legendreSym.eq_neg_one_iff]
    rwa [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The character attached to a prime discriminant takes each of the values `±1` at some natural
number. -/
theorem exists_primeDiscriminantCharFun_eq {P : ℤ} (hP : IsPrimeDiscriminant P) (ε : ℤˣ) :
    ∃ a : ℕ, primeDiscriminantCharFun P a = ε := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨1, by simp⟩
  · simpa using exists_primeDiscriminantCharFun_eq_neg_one hP

/-! ### Prescribing several characters at once -/

/-- **Distinct prime discriminants have coprime moduli.** If `P ≠ Q` are prime discriminants that
are not two distinct even ones, then `|P|` and `|Q|` are coprime. The proviso is necessary: the
even prime discriminants `-4`, `8` and `-8` all lie over `2`. -/
theorem natAbs_coprime_natAbs_of_ne {P Q : ℤ} (hP : IsPrimeDiscriminant P)
    (hQ : IsPrimeDiscriminant Q)
    (heven : IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q) (hne : P ≠ Q) :
    Nat.Coprime P.natAbs Q.natAbs := by
  refine Nat.coprime_of_dvd' fun k hk hkP hkQ => absurd ?_ hne
  have hkP' : (k : ℤ) ∣ P := Int.natCast_dvd.mpr hkP
  have hkQ' : (k : ℤ) ∣ Q := Int.natCast_dvd.mpr hkQ
  rw [natCast_dvd_primeDiscriminant_iff hP hk] at hkP'
  rw [natCast_dvd_primeDiscriminant_iff hQ hk] at hkQ'
  exact eq_of_primeDiscriminantPrime_eq hP hQ heven (hkP'.symm.trans hkQ')

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
    Int.natAbs_ne_zero.mpr (hs P hP).isFundamentalDiscriminant.ne_zero
  have hcop : Set.Pairwise (↑s : Set ℤ) (Function.onFun Nat.Coprime fun P : ℤ => P.natAbs) :=
    fun P hP Q hQ hne => natAbs_coprime_natAbs_of_ne (hs P hP) (hs Q hQ) (heven P hP Q hQ) hne
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
    Int.natAbs_ne_zero.mpr (hs P hP).isFundamentalDiscriminant.ne_zero
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
