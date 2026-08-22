/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.GaloisGroup
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.TwoRank
import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.RamifiedPrimes
import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Quadratic

/-!
# The relative candidate-genus-field Galois group has the same order as `Cl / Cl²`

For an imaginary quadratic field `K = ℚ(√d)` (`d < 0` squarefree) let `K_gen` be its candidate
genus field. This file records that the relative Galois group `Gal(K_gen/K)` has the same order as
the maximal elementary-`2` quotient `Cl(K) / Cl(K)²` of the ideal class group: both equal
`2 ^ (t - 1)`, where `t` is the number of rational primes ramifying in `K`.

This is the numerical content of the genus-theoretic summit isomorphism
`Gal(K_gen/K) ≅ Cl(K) / Cl(K)²` — the two sides have equal cardinality — established **without class
field theory**, by combining the field-theoretic relative degree `[K_gen : K] = 2 ^ (t - 1)`
(`card_aut_candidateGenusField_over_base`) with the class-group `2`-rank theorem
`2-rank Cl(K) = t - 1` (`twoRank_eq_ncard_ramifiedPrimes_sub_one`). The isomorphism itself needs the
Artin reciprocity map and is not proved here.

See D. A. Cox, *Primes of the Form x² + ny²*, §6.A, and F. Lemmermeyer, *Reciprocity Laws: From
Euler to Eisenstein*, §2.2.

## Main result

* `TauCeti.Multiquadratic.card_aut_candidateGenusField_over_base_eq_two_pow_twoRank`: for imaginary
  `K`, `|Gal(K_gen/K)| = 2 ^ (2-rank Cl(K)) = |Cl(K)/Cl(K)²|`.
-/

public section

open Polynomial
open scoped NumberField

namespace TauCeti.Multiquadratic

variable {d : ℤ}

/-- **The relative candidate-genus-field Galois group has order `2 ^ (2-rank Cl(K))`.** For an
imaginary quadratic field `K = ℚ(√d)` (`d < 0` squarefree), `|Gal(K_gen/K)|` equals
`2 ^ (2-rank Cl(K))`, which is the cardinality `|Cl(K)/Cl(K)²|`; both are `2 ^ (t - 1)`, where `t`
is the number of rational primes ramifying in `K`. This is the
numerical content of the summit isomorphism `Gal(K_gen/K) ≅ Cl(K)/Cl(K)²` — the two sides have equal
order — established without class field theory. -/
theorem card_aut_candidateGenusField_over_base_eq_two_pow_twoRank
    (hd : Squarefree d) (hneg : d < 0) :
    Nat.card (candidateGenusField hd ≃ₐ[candidateGenusFieldBase hd] candidateGenusField hd) =
      2 ^ TauCeti.ClassGroup.twoRank (𝓞 (candidateGenusFieldBase hd)) := by
  have hnsq : ¬ IsSquare ((d : ℤ) : ℚ) := by
    rintro ⟨r, hr⟩
    have h1 : (0 : ℚ) ≤ ((d : ℤ) : ℚ) := hr ▸ mul_self_nonneg r
    have h2 : ((d : ℤ) : ℚ) < 0 := by exact_mod_cast hneg
    linarith
  have : NumberField (candidateGenusFieldBase hd) :=
    NumberField.of_intermediateField (candidateGenusFieldBase hd)
  rw [card_aut_candidateGenusField_over_base hd hnsq,
    twoRank_eq_ncard_ramifiedPrimes_sub_one (minpoly_candidateGenusFieldBaseGen hd hnsq)
      (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd hneg,
    card_genusPrimeDiscriminants_eq_ncard_ramifiedPrimes
      (minpoly_candidateGenusFieldBaseGen hd hnsq)
      (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd]

end TauCeti.Multiquadratic
