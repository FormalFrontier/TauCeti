/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.RelativeDegree
public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.GaloisGroup

/-!
# The relative Galois group of the candidate genus field over `ℚ(√d)`

`CandidateGenusField/GaloisGroup` shows the candidate genus field `K_gen` is abelian Galois over
`ℚ`, with `|Gal(K_gen/ℚ)| = 2 ^ t` (`t = (genusPrimeDiscriminants hd).card`).
`CandidateGenusField/RelativeDegree` shows `[K_gen : ℚ(√d)] = 2 ^ (t - 1)` over the embedded
quadratic base `candidateGenusFieldBase`. Since `K_gen / ℚ` is Galois, it is Galois over every
intermediate field, so this file reads off the order of the relative Galois group:

`|Gal(K_gen / ℚ(√d))| = 2 ^ (t - 1)`.

For *imaginary* `d` this is the left-hand side of the genus-theory summit isomorphism
`Gal(K_gen / ℚ(√d)) ≅ Cl/Cl²`. For *real* `d` the uniform `2 ^ (t - 1)` count matches the **narrow**
class group instead (the ordinary `Cl/Cl²` can be smaller, since `K_gen` may ramify at the infinite
places). Identifying `K_gen` with the relevant genus field, and building the class-group side, is
later work; the class-group infrastructure lives in `NumberTheory/ClassGroup`.

The genus-field description is classical; see D. A. Cox, *Primes of the Form x² + ny²*, and
F. Lemmermeyer, *Reciprocity Laws*.

(`K_gen` is moreover abelian over `ℚ(√d)` — that instance is already supplied generically by
Mathlib for intermediate fields of an abelian Galois extension.)

## Main results

* `TauCeti.Multiquadratic.card_aut_candidateGenusField_over_candidateGenusFieldBase`:
  `|Gal(K_gen / ℚ(√d))| = 2 ^ (t - 1)` when `d` is not a rational square.
-/

public section

namespace TauCeti.Multiquadratic

/-- **Order of the relative Galois group of the candidate genus field over `ℚ(√d)`.** If the
squarefree integer `d` is not a rational square, then `K_gen` is Galois over its embedded quadratic
base `ℚ(√d)` (as an intermediate field of the Galois extension `K_gen / ℚ`), and its relative Galois
group has order `2 ^ (t - 1)`, where `t = (genusPrimeDiscriminants hd).card`. This is the
group-order shadow of the genus-theory summit isomorphism, which for imaginary `d` is
`Gal(K_gen / ℚ(√d)) ≅ Cl(ℚ(√d))/Cl(ℚ(√d))²` (for real `d` the count matches the narrow class group).
It is the relative analogue of the absolute `card_aut_candidateGenusField = 2 ^ t`. -/
theorem card_aut_candidateGenusField_over_candidateGenusFieldBase {d : ℤ} (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    Nat.card (candidateGenusField hd ≃ₐ[candidateGenusFieldBase hd] candidateGenusField hd)
      = 2 ^ ((genusPrimeDiscriminants hd).card - 1) := by
  rw [IsGalois.card_aut_eq_finrank,
    finrank_candidateGenusField_over_candidateGenusFieldBase hd hnsq]

end TauCeti.Multiquadratic
