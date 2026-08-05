/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

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

## Main results

* `TauCeti.Multiquadratic.isUnramifiedIn_iff_not_dvd_fundamentalDiscriminant`.
* `TauCeti.Multiquadratic.isUnramifiedIn_iff_not_dvd_of_not_dvd_two`: odd primes.
* `TauCeti.Multiquadratic.isUnramifiedIn_two_iff_mod_four_eq_one`: the prime `2`.
-/

public section

open Polynomial
open scoped NumberField

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

end TauCeti.Multiquadratic
