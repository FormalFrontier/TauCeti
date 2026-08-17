/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Factorization
public import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification
import Mathlib.Algebra.BigOperators.Associated

/-!
# Ramification of primes in a quadratic field

For a quadratic number field `K = ℚ(√d)` (given by `θ : 𝓞 K` with `minpoly ℤ θ = X² - d` and
`Algebra.adjoin ℚ {θ} = ⊤`, `d` squarefree), a rational prime `p` ramifies iff it divides the
discriminant, which is `fundamentalDiscriminant d`. Concretely:

* `p` is unramified in `𝓞 K` iff `p ∤ fundamentalDiscriminant d`;
* for `p ∤ 2` (an odd prime up to sign), `p` is unramified iff `p ∤ d` — i.e. the ramified odd
  primes are exactly those dividing the radicand `d`.

This is the finite-prime half of the Layer-1 ramified-prime behaviour of the multiquadratic
roadmap. It combines Mathlib's `NumberField.not_dvd_discr_iff_isUnramifiedIn` with the quadratic
discriminant computation `TauCeti.Multiquadratic.discr_eq_fundamentalDiscriminant`.

The second half of the file counts the ramified primes. Writing `fundamentalDiscriminant d` as a
product of prime discriminants (`IsFundamentalDiscriminant.exists_finset_primeDiscriminant`), each
factor contributes exactly one ramified prime — the prime `primeDiscriminantPrime` lying under it —
and distinct factors contribute distinct primes. So the number `t` of ramified primes of `ℚ(√d)` is
the number of prime discriminants in that factorization: the `t` of the genus-theory `2`-rank
formula and of the degree `2 ^ t` of the candidate genus field. The one-factor case is recorded
separately: a single prime ramifies in the quadratic field of a prime discriminant, which is what
the name "prime discriminant" refers to.

## Main results

* `TauCeti.Multiquadratic.isUnramifiedIn_iff_not_dvd_fundamentalDiscriminant`.
* `TauCeti.Multiquadratic.isUnramifiedIn_iff_not_dvd_of_not_dvd_two`: odd primes.
* `TauCeti.Multiquadratic.isUnramifiedIn_two_iff_mod_four_eq_one`: the prime `2`.
* `TauCeti.Multiquadratic.ramifiedPrimes_eq_singleton`: exactly one prime ramifies in the quadratic
  field of a prime discriminant.
* `TauCeti.Multiquadratic.ramifiedPrimes_eq_image`: the ramified primes of `ℚ(√d)` are the primes
  under the prime discriminants dividing its discriminant.
* `TauCeti.Multiquadratic.ncard_ramifiedPrimes_eq_card`: hence there are as many ramified primes as
  prime-discriminant factors.
* `TauCeti.Multiquadratic.map_span_eq_sq_of_dvd_fundamentalDiscriminant`: a prime dividing the
  discriminant is totally ramified, `p 𝓞 K = 𝔭 ^ 2`.
* `TauCeti.Multiquadratic.map_span_primeDiscriminantPrime_eq_sq`: the same for the single prime
  ramifying in the quadratic field of a prime discriminant.
-/

public section

open Polynomial
open scoped NumberField
open NumberField (ramifiedPrimes)

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **Ramification via the discriminant.** A rational prime `p` is unramified in `𝓞 K` iff it does
not divide `fundamentalDiscriminant d` (the field discriminant). -/
theorem isUnramifiedIn_iff_not_dvd_fundamentalDiscriminant (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) {p : ℤ} (hp : Prime p) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {p}) ↔ ¬ p ∣ fundamentalDiscriminant d := by
  rw [← discr_eq_fundamentalDiscriminant hmin hgen hsf]
  exact (NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) hp).symm

/-- **The ramified odd primes are the divisors of the radicand.** For a prime `p ∤ 2`, `p` is
unramified in `𝓞 K` iff `p ∤ d`. -/
theorem isUnramifiedIn_iff_not_dvd_of_not_dvd_two (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) {p : ℤ} (hp : Prime p)
    (hp2 : ¬ p ∣ 2) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {p}) ↔ ¬ p ∣ d := by
  rw [isUnramifiedIn_iff_not_dvd_fundamentalDiscriminant hmin hgen hsf hp,
    dvd_fundamentalDiscriminant_iff (hp.coprime_iff_not_dvd.mpr hp2)]

/-- **`2` ramifies iff `d ≢ 1 (mod 4)`.** The prime `2` is unramified in `𝓞 K` iff
`d ≡ 1 (mod 4)`. -/
theorem isUnramifiedIn_two_iff_mod_four_eq_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(2 : ℤ)}) ↔ d % 4 = 1 := by
  rw [isUnramifiedIn_iff_not_dvd_fundamentalDiscriminant hmin hgen hsf Int.prime_two,
    two_not_dvd_fundamentalDiscriminant_iff_mod_four_eq_one]

/-! ### Counting the ramified primes -/

/-- **The ramified primes of `ℚ(√d)`.** A natural prime lies in `ramifiedPrimes K` exactly when it
divides `fundamentalDiscriminant d`. -/
theorem mem_ramifiedPrimes_iff_dvd_fundamentalDiscriminant (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) {p : ℕ} (hp : p.Prime) :
    p ∈ ramifiedPrimes K ↔ (p : ℤ) ∣ fundamentalDiscriminant d := by
  rw [NumberField.mem_ramifiedPrimes_iff_dvd_discr hp,
    discr_eq_fundamentalDiscriminant hmin hgen hsf]

/-- **Exactly one rational prime ramifies in the quadratic field of a prime discriminant.** If `D`
is a prime discriminant and `K = ℚ(√(primeDiscriminantRadicand D))`, then the ramified primes of `K`
are the single prime `primeDiscriminantPrime D` lying under `D`. This is the defining property of a
prime discriminant, and the base case of the count below. -/
theorem ramifiedPrimes_eq_singleton {D : ℤ} (hD : IsPrimeDiscriminant D)
    (hmin : minpoly ℤ θ = X ^ 2 - C (primeDiscriminantRadicand D))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ramifiedPrimes K = {primeDiscriminantPrime D} := by
  have key : ∀ p : ℕ, p.Prime → (p ∈ ramifiedPrimes K ↔ p = primeDiscriminantPrime D) := by
    intro p hp
    rw [mem_ramifiedPrimes_iff_dvd_fundamentalDiscriminant hmin hgen
        (squarefree_primeDiscriminantRadicand hD) hp,
      fundamentalDiscriminant_primeDiscriminantRadicand hD,
      natCast_dvd_primeDiscriminant_iff hD hp]
  ext p
  rw [Set.mem_singleton_iff]
  exact ⟨fun hp => (key p (NumberField.prime_of_mem_ramifiedPrimes hp)).mp hp,
    fun hp => (key p (hp ▸ prime_primeDiscriminantPrime hD)).mpr hp⟩

variable {s : Finset ℤ}

/-- **The ramified primes of `ℚ(√d)` are the primes under the prime discriminants dividing its
discriminant.** If `s` is a finite set of prime discriminants with product
`fundamentalDiscriminant d`, then the ramified primes of `K = ℚ(√d)` are exactly the primes
`primeDiscriminantPrime P` for `P ∈ s`: a prime divides the product iff it divides some factor, and
a prime discriminant has just one prime divisor. -/
theorem ramifiedPrimes_eq_image (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d)
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P) (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d) :
    ramifiedPrimes K = ↑(s.image primeDiscriminantPrime) := by
  classical
  have hmem : ∀ p : ℕ, p.Prime →
      (p ∈ ramifiedPrimes K ↔ ∃ P ∈ s, p = primeDiscriminantPrime P) := by
    intro p hp
    rw [mem_ramifiedPrimes_iff_dvd_fundamentalDiscriminant hmin hgen hsf hp, ← hprod,
      (Nat.prime_iff_prime_int.mp hp).dvd_finsetProd_iff]
    exact exists_congr fun P => and_congr_right fun hP =>
      natCast_dvd_primeDiscriminant_iff (hs P hP) hp
  ext p
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  constructor
  · intro hp
    obtain ⟨P, hP, hpP⟩ := (hmem p (NumberField.prime_of_mem_ramifiedPrimes hp)).mp hp
    exact ⟨P, hP, hpP.symm⟩
  · rintro ⟨P, hP, rfl⟩
    exact (hmem _ (prime_primeDiscriminantPrime (hs P hP))).mpr ⟨P, hP, rfl⟩

/-- **The number of ramified primes of `ℚ(√d)` is the number of prime discriminants dividing its
discriminant.** This is the `t` of genus theory: the exponent in the degree `2 ^ t` of the candidate
genus field, and the `t` of the `2`-rank formula `t - 1`. Distinct prime-discriminant factors give
distinct ramified primes because only the three even prime discriminants share a prime, and `s`
contains at most one of them. -/
theorem ncard_ramifiedPrimes_eq_card (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d)
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q)
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d) :
    (ramifiedPrimes K).ncard = s.card := by
  classical
  rw [ramifiedPrimes_eq_image hmin hgen hsf hs hprod, Set.ncard_coe_finset,
    Finset.card_image_of_injOn (injOn_primeDiscriminantPrime hs heven)]

/-- **The ramified primes of `ℚ(√d)`, counted by a prime-discriminant factorization of the
discriminant.** Packages `ncard_ramifiedPrimes_eq_card` with the existence of the factorization, so
a caller need only supply `d` squarefree together with a quadratic presentation of `K`. -/
theorem exists_finset_primeDiscriminant_ncard_ramifiedPrimes (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) :
    ∃ s : Finset ℤ, (∀ P ∈ s, IsPrimeDiscriminant P) ∧
      ∏ P ∈ s, P = fundamentalDiscriminant d ∧ (ramifiedPrimes K).ncard = s.card := by
  obtain ⟨s, hs, heven, hprod⟩ :=
    (isFundamentalDiscriminant_fundamentalDiscriminant hsf).exists_finset_primeDiscriminant
  exact ⟨s, hs, hprod, ncard_ramifiedPrimes_eq_card hmin hgen hsf hs heven hprod⟩

/-! ### Total ramification

A ramified prime of a quadratic field is *totally* ramified: it has a single prime above it, with
ramification index `2`. This is `NumberField.map_span_eq_sq_of_mem_ramifiedPrimes`, read
here through the discriminant criterion above. -/

variable {p : ℕ} {𝔭 : Ideal (𝓞 K)} [𝔭.IsPrime] [𝔭.LiesOver (Ideal.span {(p : ℤ)})]

/-- **A prime dividing the discriminant of `ℚ(√d)` is totally ramified.** If the rational prime `p`
divides `fundamentalDiscriminant d` and `𝔭` is a prime of `𝓞 K` above `p`, then
`e(𝔭 ∣ p) = 2`. -/
theorem ramificationIdx_eq_two_of_dvd_fundamentalDiscriminant (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ fundamentalDiscriminant d) : 𝔭.ramificationIdx ℤ = 2 :=
  NumberField.ramificationIdx_eq_two_of_mem_ramifiedPrimes
    (NumberField.finrank_rat_eq_two hmin hgen)
    ((mem_ramifiedPrimes_iff_dvd_fundamentalDiscriminant hmin hgen hsf hp).mpr hdvd) 𝔭

/-- **`p 𝓞 K = 𝔭 ^ 2` at a prime dividing the discriminant of `ℚ(√d)`.** -/
theorem map_span_eq_sq_of_dvd_fundamentalDiscriminant (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ fundamentalDiscriminant d) :
    (Ideal.span {(p : ℤ)} : Ideal ℤ).map (algebraMap ℤ (𝓞 K)) = 𝔭 ^ 2 :=
  NumberField.map_span_eq_sq_of_mem_ramifiedPrimes
    (NumberField.finrank_rat_eq_two hmin hgen)
    ((mem_ramifiedPrimes_iff_dvd_fundamentalDiscriminant hmin hgen hsf hp).mpr hdvd) 𝔭

/-- **The quadratic field of a prime discriminant is totally ramified at its one ramified prime.**
For a prime discriminant `D` and `K = ℚ(√(primeDiscriminantRadicand D))`, the prime
`primeDiscriminantPrime D` generates the square of the unique prime of `𝓞 K` above it. This is the
local picture at the generators of the candidate genus field. -/
theorem map_span_primeDiscriminantPrime_eq_sq {D : ℤ} (hD : IsPrimeDiscriminant D)
    (hmin : minpoly ℤ θ = X ^ 2 - C (primeDiscriminantRadicand D))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {𝔮 : Ideal (𝓞 K)} [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(primeDiscriminantPrime D : ℤ)})] :
    (Ideal.span {(primeDiscriminantPrime D : ℤ)} : Ideal ℤ).map (algebraMap ℤ (𝓞 K)) = 𝔮 ^ 2 :=
  NumberField.map_span_eq_sq_of_mem_ramifiedPrimes
    (NumberField.finrank_rat_eq_two hmin hgen)
    (by rw [ramifiedPrimes_eq_singleton hD hmin hgen]; exact rfl) 𝔮

end TauCeti.Multiquadratic
