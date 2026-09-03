/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Quadratic
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Ramification
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Ramification

/-!
# The candidate genus field is unramified over `ℚ(√d)` at the finite places

For a squarefree integer `d`, `candidateGenusField hd` is the compositum of the quadratic fields
attached to the prime discriminants dividing `fundamentalDiscriminant d`, and
`candidateGenusFieldBase hd` is the copy of `K = ℚ(√d)` inside it. This file proves that, for such
a `d` that is moreover not a rational square, every prime of `𝓞 K` is unramified in the candidate
genus field: it is an unramified extension of `ℚ(√d)` at all finite places. This is the defining
property of the genus field at the finite places, and the half of the genus-field identification
the roadmap flags as the trap, since it is exactly where ramification at `2` and at the primes
dividing `d` has to be controlled.

The work is done by the general criterion
`TauCeti.Multiquadratic.isUnramifiedIn_of_forall_ramificationIdx_eq_two`: a subfield of a
prime-discriminant compositum in which every prime belonging to a factor already has ramification
index `2` carries all the ramification, so the compositum is unramified over it. Here that
subfield is the quadratic base, and the hypothesis is the total ramification of `ℚ(√d)` at the
primes dividing its discriminant, which are exactly the primes of the prime-discriminant factors.

An imaginary `d` is in particular not a rational square (`not_isSquare_of_neg`), and the base is
then totally complex, hence unramified at the infinite places too
(`isUnramifiedAtInfinitePlaces_candidateGenusField`), so for `d < 0` the two results together give
unramifiedness at *every* place: the candidate genus field of an imaginary quadratic field is an
everywhere-unramified abelian extension of it, so it lies inside the Hilbert class field. What
remains for the genus-field identification is maximality — that it is the largest such extension
abelian over `ℚ` — and the isomorphism `Gal(K_gen/K) ≅ Cl(K)/Cl(K)²`.

The description of the genus field as the prime-discriminant compositum is classical; see
D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*.

## Main result

* `TauCeti.Multiquadratic.isUnramifiedIn_candidateGenusField`: for squarefree `d` that is not a
  rational square, every prime of `𝓞 ℚ(√d)` is unramified in the candidate genus field.
-/

public section

open NumberField

open scoped NumberField

namespace TauCeti.Multiquadratic

variable {d : ℤ}

/-- **The candidate genus field is unramified over `ℚ(√d)` at every finite place.** For squarefree
`d` that is not a rational square, every prime of the ring of integers of the embedded base
`ℚ(√d)` is unramified in the ring of integers of `candidateGenusField hd`.

This is the finite-place half of the genus-field property of `candidateGenusField hd`. -/
theorem isUnramifiedIn_candidateGenusField (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ))
    (𝔭 : Ideal (𝓞 (candidateGenusFieldBase hd))) [𝔭.IsPrime] :
    Algebra.IsUnramifiedIn (𝓞 (candidateGenusField hd)) 𝔭 := by
  classical
  obtain ⟨hs, heven, hprod⟩ := genusPrimeDiscriminants_spec hd
  refine isUnramifiedIn_of_forall_ramificationIdx_eq_two
    (fun P : {P // P ∈ genusPrimeDiscriminants hd} => P.val) (candidateGenusFieldGen hd)
    (fun P => hs P.val P.property) (fun P Q hPQ => Subtype.ext hPQ)
    (fun P Q hP hQ => heven P.val P.property Q.val Q.property hP hQ)
    (candidateGenusFieldGen_sq hd) (adjoin_range_candidateGenusFieldGen_eq_top hd) _ 𝔭 ?_
  -- Each prime belonging to a prime-discriminant factor divides `fundamentalDiscriminant d`, so
  -- the quadratic base is totally ramified there.
  intro P hlies
  have := hlies
  have hp : (primeDiscriminantPrime P.val).Prime := prime_primeDiscriminantPrime (hs P.val P.2)
  have hdvd : ((primeDiscriminantPrime P.val : ℕ) : ℤ) ∣ fundamentalDiscriminant d :=
    (primeDiscriminantPrime_dvd (hs P.val P.2)).trans
      (hprod ▸ Finset.dvd_prod_of_mem _ P.property)
  exact ramificationIdx_eq_two_of_dvd_fundamentalDiscriminant
    (minpoly_candidateGenusFieldBaseGen hd hnsq)
    (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd hp hdvd

end TauCeti.Multiquadratic
