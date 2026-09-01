/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree

/-!
# Comparing two prime-discriminant factorizations

Let `a` and `d` be integers and write `A = fundamentalDiscriminant a`,
`D = fundamentalDiscriminant d`. Suppose `A = ∏ P ∈ u, P` and `D = ∏ P ∈ s, P` are factorizations
into prime discriminants, at most one member of each being even
(`IsFundamentalDiscriminant.exists_finset_primeDiscriminant` produces such factorizations). This
file gives a criterion for `u ⊆ s`, that is, for the quadratic field `ℚ(√a)` to sit inside the
compositum of the prime-discriminant quadratic fields attached to `s`:

* every rational prime dividing `A` divides `D`, and
* if `2 ∣ A` then `2 ∤ fundamentalDiscriminant c`, where `c` is any integer with `a * d = c * e ^ 2`
  — that is, `ℚ(√(ad))` is unramified at `2`.

These are exactly the two constraints that the maximality argument for the genus field extracts
from ramification theory (`TauCeti.Multiquadratic.dvd_fundamentalDiscriminant_base_of_dvd_subfield`
and `TauCeti.Multiquadratic.not_dvd_fundamentalDiscriminant_mul_of_dvd_subfield`), so the theorem
below is the arithmetic half of that argument, isolated from the field theory.

The odd part of the criterion is immediate: an odd prime lies under exactly one prime
discriminant, namely `p* = (-1)^((p-1)/2) p`, so a shared prime forces a shared factor. The even
part is the announced trap: `-4`, `8` and `-8` all lie over `2`, and mere divisibility cannot tell
them apart. What separates them is the second hypothesis. Writing `A = E * m` and `D = F * n` with
`E, F ∈ {-4, 8, -8}` and `m, n ≡ 1 (mod 4)` (a product of odd prime discriminants is `1` mod `4`),
one has `4a = E * m` and `4d = F * n`; a mismatch `E ≠ F` then makes `a * d` either twice an odd
number or `-4` times a number that is `1` mod `4`, and neither is `c * e ^ 2` with `c ≡ 1 (mod 4)`.

The classical statement is that the discriminant of a quadratic subfield of the genus field
divides the discriminant of the base; see D. A. Cox, *Primes of the Form x² + ny²*, §6.A, and
F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2. Divisibility of fundamental
discriminants is genuinely weaker than the subset relation proved here (`-4 ∣ 8`, yet the
quadratic field of discriminant `-4` is not the one of discriminant `8`), which is why the
conclusion is stated as `u ⊆ s`.

## Main results

* `TauCeti.Multiquadratic.IsPrimeDiscriminant.mod_four_eq_one`: an odd prime discriminant is
  `1` modulo `4`.
* `TauCeti.Multiquadratic.exists_mod_four_eq_one_four_mul_eq`: splitting the even factor off a
  prime-discriminant factorization of `fundamentalDiscriminant a` writes `4 * a = E * m` with
  `m ≡ 1 (mod 4)`.
* `TauCeti.Multiquadratic.isEvenPrimeDiscriminant_eq_of_four_mul_eq`: the even factors of two such
  factorizations agree as soon as the square class of the product is unramified at `2`.
* `TauCeti.Multiquadratic.subset_of_forall_prime_dvd_fundamentalDiscriminant`: the criterion for
  one factorization to be a subset of the other.
-/

public section

namespace TauCeti.Multiquadratic

/-- A prime discriminant other than `-4`, `8`, `-8` is congruent to `1` modulo `4`: it is the
odd prime discriminant `p*`. -/
theorem IsPrimeDiscriminant.mod_four_eq_one {P : ℤ} (hP : IsPrimeDiscriminant P)
    (hne : ¬ IsEvenPrimeDiscriminant P) : P % 4 = 1 := by
  rcases isPrimeDiscriminant_iff.mp hP with hev | ⟨_p, _hp, hodd, rfl⟩
  · exact absurd hev hne
  · exact oddPrimeDiscriminant_mod_four_eq_one hodd

/-- A product of odd prime discriminants is congruent to `1` modulo `4`. -/
theorem prod_primeDiscriminant_mod_four_eq_one {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P) (hne : ∀ P ∈ s, ¬ IsEvenPrimeDiscriminant P) :
    (∏ P ∈ s, P) % 4 = 1 :=
  Finset.prod_induction _ (fun x => x % 4 = 1)
    (fun x y hx hy => by
      have h := Int.mul_emod x y 4
      rw [hx, hy] at h
      simpa using h)
    (by norm_num) fun P hP => (hs P hP).mod_four_eq_one (hne P hP)

/-- **Splitting off the even prime discriminant.** If the prime discriminants in `u` have product
`fundamentalDiscriminant a` and at most one of them is even, then an even member `E` of `u`
satisfies `4 * a = E * m` for a complementary factor `m ≡ 1 (mod 4)`, namely the product of the
remaining (odd) prime discriminants. -/
theorem exists_mod_four_eq_one_four_mul_eq {a E : ℤ} {u : Finset ℤ}
    (hu : ∀ P ∈ u, IsPrimeDiscriminant P)
    (hue : ∀ P ∈ u, ∀ Q ∈ u, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q)
    (huprod : ∏ P ∈ u, P = fundamentalDiscriminant a)
    (hE : E ∈ u) (hEeven : IsEvenPrimeDiscriminant E) :
    ∃ m : ℤ, m % 4 = 1 ∧ 4 * a = E * m := by
  classical
  have hsplit : E * ∏ P ∈ u.erase E, P = fundamentalDiscriminant a := by
    rw [Finset.mul_prod_erase u (fun P => P) hE]; exact huprod
  refine ⟨∏ P ∈ u.erase E, P, ?_, ?_⟩
  · refine prod_primeDiscriminant_mod_four_eq_one
      (fun P hP => hu P (Finset.mem_of_mem_erase hP)) fun P hP hPev => ?_
    exact Finset.ne_of_mem_erase hP (hue P (Finset.mem_of_mem_erase hP) E hE hPev hEeven)
  · have h2 : (2 : ℤ) ∣ fundamentalDiscriminant a :=
      hsplit ▸ (two_dvd_evenPrimeDiscriminant hEeven).mul_right _
    have hmod : a % 4 ≠ 1 := fun h =>
      (two_not_dvd_fundamentalDiscriminant_iff_mod_four_eq_one a).mpr h h2
    rw [hsplit, fundamentalDiscriminant_def]
    split_ifs with h
    · exact absurd h hmod
    · rfl

/-- An odd number times a square is never twice an odd number. -/
private theorem odd_mul_sq_ne_two_mul_odd {c e x : ℤ} (hc : c % 2 = 1) (hx : x % 2 = 1) :
    c * e ^ 2 ≠ 2 * x := by
  intro h
  rcases Int.even_or_odd e with ⟨f, rfl⟩ | ⟨f, rfl⟩
  · have h' : 2 * x = 4 * (c * f ^ 2) := by rw [← h]; ring
    generalize c * f ^ 2 = k at h'
    omega
  · have h' : 2 * x = 4 * (c * f ^ 2) + 4 * (c * f) + c := by rw [← h]; ring
    generalize c * f ^ 2 = k at h'
    generalize c * f = l at h'
    omega

/-- A number that is `1` modulo `4` times a square is never `-4` times a number that is `1`
modulo `4`. -/
private theorem mod_four_mul_sq_ne_neg_four_mul {c e x : ℤ} (hc : c % 4 = 1) (hx : x % 4 = 1) :
    c * e ^ 2 ≠ -4 * x := by
  intro h
  rcases Int.even_or_odd e with ⟨f, rfl⟩ | ⟨f, rfl⟩
  · rcases Int.even_or_odd f with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · have h' : -4 * x = 16 * (c * g ^ 2) := by rw [← h]; ring
      generalize c * g ^ 2 = k at h'
      omega
    · have h' : -4 * x = 16 * (c * g ^ 2) + 16 * (c * g) + 4 * c := by rw [← h]; ring
      generalize c * g ^ 2 = k at h'
      generalize c * g = l at h'
      omega
  · have h' : -4 * x = 4 * (c * f ^ 2) + 4 * (c * f) + c := by rw [← h]; ring
    generalize c * f ^ 2 = k at h'
    generalize c * f = l at h'
    omega

/-- **The even prime discriminants of two fundamental discriminants agree** when the square class
of the product is unramified at `2`. Concretely: if `4 * a = E * m` and `4 * d = F * n` with
`E`, `F` even prime discriminants and `m ≡ n ≡ 1 (mod 4)`, and if `a * d = c * e ^ 2` with
`c ≡ 1 (mod 4)`, then `E = F`.

This is what distinguishes `-4`, `8` and `-8`, which no divisibility statement can: for instance
`4 * 3 = (-4) * (-3)` and `4 * 2 = 8 * 1`, and the product `3 * 2 = 6` has squarefree part `6`,
which is `2` modulo `4`, not `1`. -/
theorem isEvenPrimeDiscriminant_eq_of_four_mul_eq {a d c e E F m n : ℤ}
    (hE : IsEvenPrimeDiscriminant E) (hF : IsEvenPrimeDiscriminant F)
    (hm : m % 4 = 1) (hn : n % 4 = 1) (ha : 4 * a = E * m) (hd : 4 * d = F * n)
    (hade : a * d = c * e ^ 2) (hc : c % 4 = 1) : E = F := by
  have hmn : m * n % 2 = 1 :=
    Int.odd_iff.mp ((Int.odd_iff.mpr (by omega)).mul (Int.odd_iff.mpr (by omega)))
  have hmnneg : -(m * n) % 2 = 1 := by omega
  have hmn4 : m * n % 4 = 1 := by
    have h := Int.mul_emod m n 4
    rw [hm, hn] at h
    simpa using h
  have hc2 : c % 2 = 1 := by omega
  rcases hE with rfl | rfl | rfl <;> rcases hF with rfl | rfl | rfl
  · rfl
  · have hcontra : c * e ^ 2 = 2 * -(m * n) := by
      have ha : a = -m := by omega
      have hd : d = 2 * n := by omega
      rw [← hade, ha, hd]
      ring
    exact absurd hcontra (odd_mul_sq_ne_two_mul_odd hc2 hmnneg)
  · have hcontra : c * e ^ 2 = 2 * (m * n) := by
      have ha : a = -m := by omega
      have hd : d = -(2 * n) := by omega
      rw [← hade, ha, hd]
      ring
    exact absurd hcontra (odd_mul_sq_ne_two_mul_odd hc2 hmn)
  · have hcontra : c * e ^ 2 = 2 * -(m * n) := by
      have ha : a = 2 * m := by omega
      have hd : d = -n := by omega
      rw [← hade, ha, hd]
      ring
    exact absurd hcontra (odd_mul_sq_ne_two_mul_odd hc2 hmnneg)
  · rfl
  · have hcontra : c * e ^ 2 = -4 * (m * n) := by
      have ha : a = 2 * m := by omega
      have hd : d = -(2 * n) := by omega
      rw [← hade, ha, hd]
      ring
    exact absurd hcontra (mod_four_mul_sq_ne_neg_four_mul hc hmn4)
  · have hcontra : c * e ^ 2 = 2 * (m * n) := by
      have ha : a = -(2 * m) := by omega
      have hd : d = -n := by omega
      rw [← hade, ha, hd]
      ring
    exact absurd hcontra (odd_mul_sq_ne_two_mul_odd hc2 hmn)
  · have hcontra : c * e ^ 2 = -4 * (m * n) := by
      have ha : a = -(2 * m) := by omega
      have hd : d = 2 * n := by omega
      rw [← hade, ha, hd]
      ring
    exact absurd hcontra (mod_four_mul_sq_ne_neg_four_mul hc hmn4)
  · rfl

/-- **A prime-discriminant factorization sits inside another.** Let `u` and `s` be finite sets of
prime discriminants, at most one member of each being even, with products
`fundamentalDiscriminant a` and `fundamentalDiscriminant d`. If every rational prime dividing
`fundamentalDiscriminant a` divides `fundamentalDiscriminant d`, and if `2 ∣
fundamentalDiscriminant a` forces `fundamentalDiscriminant c` to be odd for some `c` with
`a * d = c * e ^ 2`, then `u ⊆ s`.

Both hypotheses are needed, and both are supplied by the ramification theory of a Galois extension
unramified over `ℚ(√d)`: the first says a prime ramifying in `ℚ(√a)` ramifies in `ℚ(√d)`, the
second that `2` does not ramify in `ℚ(√(ad))`. -/
theorem subset_of_forall_prime_dvd_fundamentalDiscriminant {a d c e : ℤ} {s u : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (hse : ∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q)
    (hsprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hu : ∀ P ∈ u, IsPrimeDiscriminant P)
    (hue : ∀ P ∈ u, ∀ Q ∈ u, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q)
    (huprod : ∏ P ∈ u, P = fundamentalDiscriminant a)
    (hade : a * d = c * e ^ 2)
    (hdvd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ fundamentalDiscriminant a →
      (p : ℤ) ∣ fundamentalDiscriminant d)
    (hodd : (2 : ℤ) ∣ fundamentalDiscriminant a → ¬ (2 : ℤ) ∣ fundamentalDiscriminant c) :
    u ⊆ s := by
  intro P hP
  have hPd : IsPrimeDiscriminant P := hu P hP
  have hpprime : (primeDiscriminantPrime P).Prime := prime_primeDiscriminantPrime hPd
  have hpa : ((primeDiscriminantPrime P : ℕ) : ℤ) ∣ fundamentalDiscriminant a :=
    huprod ▸ (primeDiscriminantPrime_dvd hPd).trans (Finset.dvd_prod_of_mem _ hP)
  have hpd : ((primeDiscriminantPrime P : ℕ) : ℤ) ∣ ∏ P ∈ s, P := by
    rw [hsprod]; exact hdvd _ hpprime hpa
  have hpZ : Prime ((primeDiscriminantPrime P : ℕ) : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hpprime)
  obtain ⟨Q, hQ, hpQ⟩ := hpZ.exists_mem_finset_dvd hpd
  have hQd : IsPrimeDiscriminant Q := hs Q hQ
  have hpq : primeDiscriminantPrime P = primeDiscriminantPrime Q :=
    (natCast_dvd_primeDiscriminant_iff hQd hpprime).mp hpQ
  have heven : IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q := by
    intro hPev hQev
    obtain ⟨m, hm, ham⟩ := exists_mod_four_eq_one_four_mul_eq hu hue huprod hP hPev
    obtain ⟨n, hn, hdn⟩ := exists_mod_four_eq_one_four_mul_eq hs hse hsprod hQ hQev
    have h2a : (2 : ℤ) ∣ fundamentalDiscriminant a := by
      rwa [primeDiscriminantPrime_of_isEvenPrimeDiscriminant hPev, Nat.cast_ofNat] at hpa
    exact isEvenPrimeDiscriminant_eq_of_four_mul_eq hPev hQev hm hn ham hdn hade
      ((two_not_dvd_fundamentalDiscriminant_iff_mod_four_eq_one c).mp (hodd h2a))
  exact eq_of_primeDiscriminantPrime_eq hPd hQd heven hpq ▸ hQ

end TauCeti.Multiquadratic
