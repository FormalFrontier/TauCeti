/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import Mathlib.Data.Int.NatAbs

/-!
# Prime-discriminant factorization of a fundamental discriminant

`FundamentalDiscriminant/Basic` supplies the *synthesis* half of the prime-discriminant/
fundamental-discriminant correspondence: a product of distinct prime discriminants with at most
one even value is a fundamental discriminant. This file supplies the **analysis** half, the
converse existence statement: every fundamental discriminant `D` is a product of a finite set of
prime discriminants, at most one of which is even.

The factorization is unique once its factors are required to be distinct. Its proof first matches
the odd factors through the unique rational prime below each prime discriminant. After cancelling
their common product, the remaining factors belong to the three-element set `{-4, 8, -8}`; its
eight subsets have pairwise distinct products, so the even factors match as well.

This is the classical prime-discriminant factorization; see D. A. Cox, *Primes of the Form
x² + ny²*, §3.B and §6.A, and F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.

This is a prerequisite for the genus-field layer, which attaches a *family* of prime discriminants
to a quadratic field `ℚ(√d)`: the square-class independence and degree theorems of
`Multiquadratic/Prime/Discriminant/Independence.lean` apply to such a family, giving a
degree-`2ᵗ` multiquadratic compositum. Turning that compositum into the genus field — defining the
genus field and identifying it with this compositum — is later work; this file only supplies the
factorization the family comes from.

The engine is `prod_oddPrimeDiscriminant_primeFactors_eq`: for an odd squarefree `x ≡ 1 (mod 4)`,
the product of the odd prime discriminants `p*` over the prime factors `p` of `x` is `x` itself.
The two sides share an absolute value (each `p*` has `|p*| = p`, and `x` is squarefree) and are
both `≡ 1 (mod 4)`, so they agree by sign uniqueness. The three shapes of a fundamental
discriminant — odd, `4 ·` odd, `8 ·` odd — then differ only in the single even prime discriminant
(`-4`, `-8`, `8`) prepended to that odd product.

## Main results

* `TauCeti.Multiquadratic.IsFundamentalDiscriminant.exists_finset_primeDiscriminant`: every
  fundamental discriminant is a product of a finite set of prime discriminants with at most one
  even value — the converse of `isFundamentalDiscriminant_prod`.
* `TauCeti.Multiquadratic.finset_primeDiscriminant_eq_of_prod_eq`: two finite sets of prime
  discriminants with the same product have the same factors.
* `TauCeti.Multiquadratic.IsFundamentalDiscriminant.existsUnique_finset_primeDiscriminant`: every
  fundamental discriminant has a unique factorization into a finite set of prime discriminants.
-/

public section

namespace TauCeti.Multiquadratic

open Finset

/-- Sign uniqueness modulo `4`: two integers with the same absolute value that are both
`≡ 1 (mod 4)` are equal (they cannot be negatives of each other). -/
private lemma eq_of_natAbs_eq_of_mod_four_eq_one {x y : ℤ} (h : x.natAbs = y.natAbs)
    (hx : x % 4 = 1) (hy : y % 4 = 1) : x = y := by
  rcases Int.natAbs_eq_natAbs_iff.mp h with h1 | h1
  · exact h1
  · omega

/-- **The odd prime discriminants recover the odd `≡ 1 (mod 4)` part.** For an odd squarefree
integer `x ≡ 1 (mod 4)`, the product of the odd prime discriminants `p*` over the prime factors
`p` of `x` equals `x`. -/
private lemma prod_oddPrimeDiscriminant_primeFactors_eq {x : ℤ} (hsf : Squarefree x)
    (hodd : Odd x) (hmod : x % 4 = 1) :
    ∏ p ∈ x.natAbs.primeFactors, oddPrimeDiscriminant p = x := by
  have hoddn : Odd x.natAbs := Int.natAbs_odd.mpr hodd
  have hsfn : Squarefree x.natAbs := Int.squarefree_natAbs.mpr hsf
  have hnat : (∏ p ∈ x.natAbs.primeFactors, oddPrimeDiscriminant p).natAbs = x.natAbs :=
    calc (∏ p ∈ x.natAbs.primeFactors, oddPrimeDiscriminant p).natAbs
        = ∏ p ∈ x.natAbs.primeFactors, (oddPrimeDiscriminant p).natAbs :=
          map_prod Int.natAbsHom _ _
      _ = ∏ p ∈ x.natAbs.primeFactors, p :=
          Finset.prod_congr rfl fun p _ => oddPrimeDiscriminant_natAbs p
      _ = x.natAbs := Nat.prod_primeFactors_of_squarefree hsfn
  have hmod4 : (∏ p ∈ x.natAbs.primeFactors, oddPrimeDiscriminant p) % 4 = 1 :=
    prod_oddPrimeDiscriminant_mod_four_eq_one
      (fun p hp => Odd.of_dvd_nat hoddn (Nat.dvd_of_mem_primeFactors hp))
  exact eq_of_natAbs_eq_of_mod_four_eq_one hnat hmod4 hmod

/-- The image family `{p* : p ∣ n}` of odd prime discriminants over the prime factors of an odd
`n`: each member is a non-even prime discriminant, and the assignment is injective, so its `Finset`
product is the indexed product over the prime factors. -/
private lemma oddPrimeDiscriminant_image_prod {n : ℕ} (hn : Odd n) :
    (∀ P ∈ n.primeFactors.image oddPrimeDiscriminant, IsPrimeDiscriminant P ∧
        ¬ IsEvenPrimeDiscriminant P) ∧
      ∏ P ∈ n.primeFactors.image oddPrimeDiscriminant, P =
        ∏ p ∈ n.primeFactors, oddPrimeDiscriminant p := by
  refine ⟨fun P hP => ?_, ?_⟩
  · rw [Finset.mem_image] at hP
    obtain ⟨p, hp, rfl⟩ := hP
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpo := Odd.of_dvd_nat hn (Nat.dvd_of_mem_primeFactors hp)
    exact ⟨isPrimeDiscriminant_oddPrimeDiscriminant hpp hpo,
      not_isEvenPrimeDiscriminant_oddPrimeDiscriminant hpo⟩
  · refine Finset.prod_image fun p _ q _ h => ?_
    have : (oddPrimeDiscriminant p).natAbs = (oddPrimeDiscriminant q).natAbs := by rw [h]
    simpa only [oddPrimeDiscriminant_natAbs] using this

/-- Prepend one even prime discriminant `e` to the odd-prime-discriminant image family of an odd
`n`, packaged as a finset of prime discriminants with `e` the unique even member and product `D`.
This is the shared body of the three even-discriminant branches of the main theorem. -/
private lemma exists_finset_insert_evenPrimeDiscriminant {D e : ℤ} {n : ℕ} (hn : Odd n)
    (hePD : IsPrimeDiscriminant e) (heE : IsEvenPrimeDiscriminant e)
    (hprod : e * ∏ p ∈ n.primeFactors, oddPrimeDiscriminant p = D) :
    ∃ s : Finset ℤ, (∀ P ∈ s, IsPrimeDiscriminant P) ∧
      (∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q) ∧
      ∏ P ∈ s, P = D := by
  obtain ⟨himg, hprodimg⟩ := oddPrimeDiscriminant_image_prod hn
  have hne : e ∉ n.primeFactors.image oddPrimeDiscriminant := fun hmem => (himg _ hmem).2 heE
  refine ⟨insert e (n.primeFactors.image oddPrimeDiscriminant), ?_, ?_, ?_⟩
  · intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact hePD
    · exact (himg P hP).1
  · intro P hP Q hQ hPe hQe
    have hPeq : P = e := (Finset.mem_insert.mp hP).resolve_right fun h => (himg P h).2 hPe
    have hQeq : Q = e := (Finset.mem_insert.mp hQ).resolve_right fun h => (himg Q h).2 hQe
    rw [hPeq, hQeq]
  · rw [Finset.prod_insert hne, hprodimg]; exact hprod

/-- **Analysis half of the prime-discriminant correspondence.** Every fundamental discriminant
`D` is a product of a finite set of prime discriminants, at most one of which is even. This is the
converse of `TauCeti.Multiquadratic.isFundamentalDiscriminant_prod`. -/
theorem IsFundamentalDiscriminant.exists_finset_primeDiscriminant {D : ℤ}
    (hD : IsFundamentalDiscriminant D) :
    ∃ s : Finset ℤ, (∀ P ∈ s, IsPrimeDiscriminant P) ∧
      (∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q) ∧
      ∏ P ∈ s, P = D := by
  rcases hD.mod_four_eq_zero_or_one with h0 | h1
  · -- `D = 4 * m`, `m` squarefree, `m ≡ 2` or `3 (mod 4)`.
    have hsf : Squarefree (D / 4) := hD.squarefree_div_four h0
    have hmm : D / 4 % 4 = 2 ∨ D / 4 % 4 = 3 := hD.div_four_mod_four_eq_two_or_three h0
    have hDm : D = 4 * (D / 4) := by omega
    set m := D / 4 with hm
    rcases hmm with hm2 | hm3
    · -- `m ≡ 2 (mod 4)`: write `m = 2 * k` with `k` odd; the even factor is `±8`.
      have hk2 : m = 2 * (m / 2) := by omega
      set k := m / 2 with hk
      have hkodd : Odd k := Int.odd_iff.mpr (by omega)
      have hksf : Squarefree k := hsf.squarefree_of_dvd ⟨2, by omega⟩
      have hD8 : D = 8 * k := by omega
      rcases (by omega : k % 4 = 1 ∨ k % 4 = 3) with hk1 | hk3
      · -- `k ≡ 1 (mod 4)`: even factor `8`, odd product `k`.
        have hcore := prod_oddPrimeDiscriminant_primeFactors_eq hksf hkodd hk1
        exact exists_finset_insert_evenPrimeDiscriminant (Int.natAbs_odd.mpr hkodd)
          isPrimeDiscriminant_eight (by simp) (by rw [hcore]; omega)
      · -- `k ≡ 3 (mod 4)`: even factor `-8`, odd product `-k`.
        have hcore := prod_oddPrimeDiscriminant_primeFactors_eq hksf.neg hkodd.neg (by omega)
        rw [Int.natAbs_neg] at hcore
        exact exists_finset_insert_evenPrimeDiscriminant (Int.natAbs_odd.mpr hkodd)
          isPrimeDiscriminant_neg_eight (by simp) (by rw [hcore]; omega)
    · -- `m ≡ 3 (mod 4)`, `m` odd: even factor `-4`, odd product `-m`.
      have hmodd : Odd m := Int.odd_iff.mpr (by omega)
      have hcore := prod_oddPrimeDiscriminant_primeFactors_eq hsf.neg hmodd.neg (by omega)
      rw [Int.natAbs_neg] at hcore
      exact exists_finset_insert_evenPrimeDiscriminant (Int.natAbs_odd.mpr hmodd)
        isPrimeDiscriminant_neg_four (by simp) (by rw [hcore]; omega)
  · -- `D ≡ 1 (mod 4)`, `D` odd squarefree: no even factor.
    have hsf : Squarefree D := hD.squarefree_of_mod_four_eq_one h1
    have hodd : Odd D := Int.odd_iff.mpr (by omega)
    obtain ⟨himg, hprodimg⟩ := oddPrimeDiscriminant_image_prod (Int.natAbs_odd.mpr hodd)
    refine ⟨D.natAbs.primeFactors.image oddPrimeDiscriminant, fun P hP => (himg P hP).1, ?_, ?_⟩
    · intro P hP Q _ hPe _
      exact absurd hPe (himg P hP).2
    · rw [hprodimg]
      exact prod_oddPrimeDiscriminant_primeFactors_eq hsf hodd h1

/-- An odd prime-discriminant factor of one product occurs in any equal prime-discriminant
product.  The rational prime below an odd prime discriminant determines it uniquely. -/
private theorem mem_of_not_isEvenPrimeDiscriminant_of_prod_eq {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P) (ht : ∀ P ∈ t, IsPrimeDiscriminant P)
    (hprod : ∏ P ∈ s, P = ∏ P ∈ t, P) {P : ℤ} (hPs : P ∈ s)
    (hPodd : ¬ IsEvenPrimeDiscriminant P) : P ∈ t := by
  let p := primeDiscriminantPrime P
  have hp : p.Prime := prime_primeDiscriminantPrime (hs P hPs)
  have hp_prod : (p : ℤ) ∣ ∏ Q ∈ t, Q := by
    rw [← hprod]
    exact (primeDiscriminantPrime_dvd (hs P hPs)).trans (Finset.dvd_prod_of_mem id hPs)
  obtain ⟨Q, hQt, hpQ⟩ : ∃ Q ∈ t, (p : ℤ) ∣ Q :=
    ((Nat.prime_iff_prime_int.mp hp).dvd_finsetProd_iff id).mp hp_prod
  have hp_eq : primeDiscriminantPrime P = primeDiscriminantPrime Q :=
    (natCast_dvd_primeDiscriminant_iff (ht Q hQt) hp).mp hpQ
  have hPQ : P = Q := eq_of_primeDiscriminantPrime_eq (hs P hPs) (ht Q hQt)
    (fun hPeven _ => absurd hPeven hPodd) hp_eq
  rwa [hPQ]

open Classical in
/-- A finset of even prime discriminants is determined by its product. -/
private theorem finset_isEvenPrimeDiscriminant_eq_of_prod_eq {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsEvenPrimeDiscriminant P)
    (ht : ∀ P ∈ t, IsEvenPrimeDiscriminant P)
    (hprod : ∏ P ∈ s, P = ∏ P ∈ t, P) : s = t := by
  classical
  have hs_mem : s ∈ ({-4, 8, -8} : Finset ℤ).powerset := by
    rw [Finset.mem_powerset]
    intro P hP
    simpa only [Finset.mem_insert, Finset.mem_singleton, IsEvenPrimeDiscriminant] using hs P hP
  have ht_mem : t ∈ ({-4, 8, -8} : Finset ℤ).powerset := by
    rw [Finset.mem_powerset]
    intro P hP
    simpa only [Finset.mem_insert, Finset.mem_singleton, IsEvenPrimeDiscriminant] using ht P hP
  fin_cases hs_mem <;> fin_cases ht_mem
  all_goals norm_num at hprod
  all_goals rfl

/-- **Uniqueness of a prime-discriminant factorization.** Two finite sets of prime discriminants
are equal when their products are equal.

Odd factors are determined by their unique underlying rational prime. Once those common factors
are cancelled from the product equality, each remaining factor belongs to `{-4, 8, -8}`; the
products of the eight possible subsets are distinct, so the even factors match too. -/
theorem finset_primeDiscriminant_eq_of_prod_eq {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (ht : ∀ P ∈ t, IsPrimeDiscriminant P)
    (hprod : ∏ P ∈ s, P = ∏ P ∈ t, P) : s = t := by
  classical
  have hodd : s.filter (fun P => ¬ IsEvenPrimeDiscriminant P) =
      t.filter (fun P => ¬ IsEvenPrimeDiscriminant P) := by
    ext P
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hPs, hPodd⟩
      exact ⟨mem_of_not_isEvenPrimeDiscriminant_of_prod_eq hs ht hprod hPs hPodd, hPodd⟩
    · rintro ⟨hPt, hPodd⟩
      exact ⟨mem_of_not_isEvenPrimeDiscriminant_of_prod_eq ht hs hprod.symm hPt hPodd, hPodd⟩
  have hodd_ne : (∏ P ∈ s with ¬ IsEvenPrimeDiscriminant P, P) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro P hP
    rcases isPrimeDiscriminant_iff.mp (hs P (Finset.mem_filter.mp hP).1) with
      hPeven | ⟨p, hp, hPodd, rfl⟩
    · exact absurd hPeven (Finset.mem_filter.mp hP).2
    · exact oddPrimeDiscriminant_ne_zero.mpr hp.ne_zero
  have heven_prod : (∏ P ∈ s with IsEvenPrimeDiscriminant P, P) =
      ∏ P ∈ t with IsEvenPrimeDiscriminant P, P := by
    apply mul_right_cancel₀ hodd_ne
    rw [Finset.prod_filter_mul_prod_filter_not, hodd,
      Finset.prod_filter_mul_prod_filter_not, hprod]
  have heven : s.filter IsEvenPrimeDiscriminant = t.filter IsEvenPrimeDiscriminant :=
    finset_isEvenPrimeDiscriminant_eq_of_prod_eq
      (fun P hP => (Finset.mem_filter.mp hP).2)
      (fun P hP => (Finset.mem_filter.mp hP).2) heven_prod
  ext P
  by_cases hPeven : IsEvenPrimeDiscriminant P
  · simpa only [Finset.ext_iff, Finset.mem_filter, hPeven, and_true] using
      Finset.ext_iff.mp heven P
  · simpa only [Finset.ext_iff, Finset.mem_filter, hPeven, not_false_eq_true, and_true] using
      Finset.ext_iff.mp hodd P

/-- **Unique prime-discriminant factorization of a fundamental discriminant.** Every fundamental
discriminant is the product of a unique finite set of prime discriminants. -/
theorem IsFundamentalDiscriminant.existsUnique_finset_primeDiscriminant {D : ℤ}
    (hD : IsFundamentalDiscriminant D) :
    ∃! s : Finset ℤ, (∀ P ∈ s, IsPrimeDiscriminant P) ∧ ∏ P ∈ s, P = D := by
  obtain ⟨s, hs, _, hprod⟩ := hD.exists_finset_primeDiscriminant
  refine ⟨s, ⟨hs, hprod⟩, fun t ht => ?_⟩
  exact finset_primeDiscriminant_eq_of_prod_eq ht.1 hs (ht.2.trans hprod.symm)

end TauCeti.Multiquadratic
