/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Ramification
public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Basic

/-!
# Ramification of `ℚ(√d)` through its genus prime-discriminant factorization

For a quadratic number field `K = ℚ(√d)` (given by `θ : 𝓞 K` with `minpoly ℤ θ = X² - d`,
`Algebra.adjoin ℚ {θ} = ⊤`, `d` squarefree), a rational prime `p` ramifies in `𝓞 K` iff it divides
the discriminant `fundamentalDiscriminant d`. This file re-expresses that law through the chosen
factorization `genusPrimeDiscriminants hd` whose product is `fundamentalDiscriminant d` — the very
prime discriminants whose radicands generate `candidateGenusField hd`.

Since a prime divides the product iff it divides one of the factors, `p` is unramified in `𝓞 K`
exactly when it divides *none* of the genus prime discriminants. This records, at the finite places,
how the factorization that builds the candidate genus field controls the ramified primes of the
base field `ℚ(√d)` — the finite-place input to the genus-field identification.

## Main results

* `TauCeti.Multiquadratic.isUnramifiedIn_iff_forall_not_dvd_genusPrimeDiscriminant`.
-/

public section

open Polynomial
open scoped NumberField

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **Ramification via the genus factorization.** A rational prime `p` is unramified in `𝓞 K` iff it
divides none of the prime discriminants in `genusPrimeDiscriminants hd` (whose product is the field
discriminant `fundamentalDiscriminant d`). -/
theorem isUnramifiedIn_iff_forall_not_dvd_genusPrimeDiscriminant
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hd : Squarefree d) {p : ℤ} (hp : Prime p) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {p}) ↔
      ∀ P ∈ genusPrimeDiscriminants hd, ¬ p ∣ P := by
  rw [isUnramifiedIn_iff_not_dvd_fundamentalDiscriminant hmin hgen hd hp,
    ← (genusPrimeDiscriminants_spec hd).2.2, hp.dvd_finsetProd_iff]
  simp only [not_exists, not_and]

end TauCeti.Multiquadratic
