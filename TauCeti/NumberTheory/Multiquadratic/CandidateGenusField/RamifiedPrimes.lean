/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Degree
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Ramification

/-!
# The candidate genus field has degree `2 ^ t`

For a squarefree integer `d`, the degree of `candidateGenusField hd` over `ℚ` was computed in
`CandidateGenusField/Degree.lean` as `2 ^ (genusPrimeDiscriminants hd).card`, and its degree over
the embedded copy of `ℚ(√d)` in `CandidateGenusField/Relative/Degree.lean` as `2 ^ (t - 1)` for the
same `t`. Those exponents count a *chosen* prime-discriminant factorization of
`fundamentalDiscriminant d`. This file replaces them by the intrinsic invariant of `K = ℚ(√d)` that
genus theory names: the number `t` of rational primes ramifying in `K`.

That identification is `TauCeti.Multiquadratic.ncard_ramifiedPrimes_eq_card`, so all that happens
here is the substitution. Its point is that the exponents no longer depend on the choice made by
`genusPrimeDiscriminants`, and that the relative degree now reads as the classical `2 ^ (t - 1)` —
the field-theoretic half of the genus-theory `2`-rank formula, whose remaining half is the
isomorphism `Gal(K_gen/K) ≅ Cl⁺(K)/Cl⁺(K)²` with the *narrow* class group (not yet available). The
narrow class group is the right object here because `candidateGenusField` is unramified only at the
finite places; for imaginary `d` it agrees with `Cl(K)`, while for real `d` the ordinary quotient
can be smaller.

The `2 ^ (t - 1)` count for the genus field is classical; see D. A. Cox, *Primes of the Form
x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*.

## Main results

In the namespace `TauCeti.Multiquadratic`:

* `finrank_candidateGenusField_eq_two_pow_ncard_ramifiedPrimes`.
* `finrank_candidateGenusField_over_candidateGenusFieldBase_eq_two_pow_ncard_ramifiedPrimes`.
-/

public section

open Polynomial
open scoped NumberField
open NumberField (ramifiedPrimes)

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The chosen prime-discriminant factorization has as many members as `ℚ(√d)` has ramified
primes.** -/
theorem card_genusPrimeDiscriminants_eq_ncard_ramifiedPrimes
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hd : Squarefree d) :
    (genusPrimeDiscriminants hd).card = (ramifiedPrimes K).ncard :=
  have ⟨hs, heven, hprod⟩ := genusPrimeDiscriminants_spec hd
  (ncard_ramifiedPrimes_eq_card hmin hgen hd hs heven hprod).symm

/-- **The candidate genus field of `ℚ(√d)` has degree `2 ^ t` over `ℚ`**, where `t` is the number of
rational primes ramifying in `ℚ(√d)`. -/
theorem finrank_candidateGenusField_eq_two_pow_ncard_ramifiedPrimes
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hd : Squarefree d) :
    Module.finrank ℚ (candidateGenusField hd) = 2 ^ (ramifiedPrimes K).ncard := by
  rw [finrank_candidateGenusField hd,
    card_genusPrimeDiscriminants_eq_ncard_ramifiedPrimes hmin hgen hd]

/-- **The candidate genus field of `ℚ(√d)` has degree `2 ^ (t - 1)` over `ℚ(√d)`**, where `t` is the
number of rational primes ramifying in `ℚ(√d)`. This is the field-theoretic side of the genus-theory
`2`-rank formula: once `Gal(K_gen/K) ≅ Cl⁺(K)/Cl⁺(K)²` is available, it says that the elementary-`2`
quotient of the *narrow* class group has rank `t - 1`. -/
theorem finrank_candidateGenusField_over_candidateGenusFieldBase_eq_two_pow_ncard_ramifiedPrimes
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hd : Squarefree d) :
    Module.finrank (candidateGenusFieldBase hd) (candidateGenusField hd) =
      2 ^ ((ramifiedPrimes K).ncard - 1) := by
  rw [finrank_candidateGenusField_over_candidateGenusFieldBase hd
      (NumberField.not_isSquare_radicand hmin),
    card_genusPrimeDiscriminants_eq_ncard_ramifiedPrimes hmin hgen hd]

end TauCeti.Multiquadratic
