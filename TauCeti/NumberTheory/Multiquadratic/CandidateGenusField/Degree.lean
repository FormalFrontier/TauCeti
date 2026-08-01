/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Basic
import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Independence

/-!
# Degree of the candidate genus field

For a squarefree integer `d`, `candidateGenusField hd` is the compositum of the quadratic
fields attached to the prime discriminants in `genusPrimeDiscriminants hd`. This file proves
that this compositum has the full multiquadratic degree

`[candidateGenusField hd : ℚ] = 2 ^ (genusPrimeDiscriminants hd).card`.

The defining properties of `genusPrimeDiscriminants hd` say that its members are prime
discriminants and that at most one is even. Their radicands are therefore square-class
independent. The degree formula is the corresponding specialization of
`finrank_adjoin_roots_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq`.

This is the degree step in proving that the candidate genus field is multiquadratic. Identifying
this candidate with the maximal extension satisfying the genus-field ramification conditions is
later work.

The prime-discriminant description of the genus field is classical; see D. A. Cox,
*Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*.

## Main results

* `TauCeti.Multiquadratic.finiteDimensional_candidateGenusField`: the candidate genus field is a
  finite extension of `ℚ`.
* `TauCeti.Multiquadratic.finrank_candidateGenusField`: its degree over `ℚ` is `2` to the number
  of prime discriminants in its chosen factorization.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- The candidate genus field is finite-dimensional over `ℚ`. -/
noncomputable instance finiteDimensional_candidateGenusField {d : ℤ} {hd : Squarefree d} :
    FiniteDimensional ℚ (candidateGenusField hd) := by
  rw [candidateGenusField_def]
  apply finiteDimensional_adjoin
  rintro _ ⟨P, rfl⟩
  apply IsIntegral.of_pow (by norm_num : 0 < 2)
  rw [genusFieldRoot_sq]
  exact isIntegral_algebraMap

/-- **Degree of the candidate genus field.** If `d` is squarefree, adjoining the chosen square
roots of the radicands of the prime discriminants in `genusPrimeDiscriminants hd` gives an
extension of `ℚ` of degree `2 ^ (genusPrimeDiscriminants hd).card`. Thus the candidate genus
field has the full degree predicted by square-class independence. -/
theorem finrank_candidateGenusField {d : ℤ} (hd : Squarefree d) :
    Module.finrank ℚ (candidateGenusField hd) =
      2 ^ (genusPrimeDiscriminants hd).card := by
  classical
  obtain ⟨hprime, heven_unique, _⟩ := genusPrimeDiscriminants_spec hd
  rw [candidateGenusField_def]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    finrank_adjoin_roots_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq
      (fun P : {P // P ∈ genusPrimeDiscriminants hd} => P.val)
      (fun P => hprime P.val P.property) Subtype.val_injective
      (fun P Q hP hQ => heven_unique P.val P.property Q.val Q.property hP hQ)
      (genusFieldRoot hd) (fun P => by simp)

end TauCeti.Multiquadratic
