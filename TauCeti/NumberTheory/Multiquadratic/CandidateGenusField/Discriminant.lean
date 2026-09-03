/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Degree
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Compositum

/-!
# The discriminant and the ramified primes of the candidate genus field

For a squarefree integer `d`, `candidateGenusField hd` is the compositum of the quadratic fields
attached to the prime discriminants dividing `fundamentalDiscriminant d`. This file computes its
field discriminant

`|disc (candidateGenusField hd)| = ∏ |P| ^ 2 ^ (t - 1)`,

the product over the chosen prime-discriminant factors `P`, with `t` their number, and reads off
the rational primes that ramify in it: exactly the primes dividing `fundamentalDiscriminant d`,
which is to say exactly the primes that ramify in `ℚ(√d)` itself.

Both statements are the candidate-genus-field instance of the compositum discriminant formula
`TauCeti.Multiquadratic.natAbs_discr_adjoin_range_primeDiscriminantRadicands`, transported along
`adjoin_range_candidateGenusFieldGen_eq_top`; the ramification criterion is then Mathlib's
`NumberField.not_dvd_discr_iff_isUnramifiedIn`.

That the candidate genus field ramifies nowhere beyond `ℚ(√d)` is the absolute half of the
genus-field property: the relative statement, that it is unramified *over* `ℚ(√d)` at every finite
place, is proved in `CandidateGenusField/Relative/Ramification.lean` and needs the sharper local
information that the ramification index does not grow.

The prime-discriminant description of the genus field is classical; see D. A. Cox, *Primes of the
Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*.

## Main results

* `TauCeti.Multiquadratic.natAbs_discr_candidateGenusField`: the discriminant formula.
* `TauCeti.Multiquadratic.isUnramifiedIn_candidateGenusField_iff`: a rational prime is unramified
  in the candidate genus field iff it does not divide `fundamentalDiscriminant d`.
-/

public section

open IntermediateField

open scoped NumberField

namespace TauCeti.Multiquadratic

variable {d : ℤ}

/-- **The discriminant of the candidate genus field.** For squarefree `d`, the absolute value of
the field discriminant of `candidateGenusField hd` is the product of the absolute values of its
chosen prime-discriminant factors, each raised to the power `2 ^ (t - 1)` with `t` the number of
factors. This is the multiquadratic compositum formula
`natAbs_discr_adjoin_range_primeDiscriminantRadicands` applied to the chosen roots. -/
theorem natAbs_discr_candidateGenusField (hd : Squarefree d) :
    (NumberField.discr (candidateGenusField hd)).natAbs =
      ∏ P ∈ genusPrimeDiscriminants hd,
        P.natAbs ^ (2 ^ ((genusPrimeDiscriminants hd).card - 1)) := by
  classical
  obtain ⟨hs, heven, -⟩ := genusPrimeDiscriminants_spec hd
  have h := natAbs_discr_adjoin_range_primeDiscriminantRadicands
    (ι := {P // P ∈ genusPrimeDiscriminants hd}) (L := candidateGenusField hd)
    (fun P => P.val) (fun P => hs P.val P.property) Subtype.val_injective
    (fun P Q hP hQ => heven P.val P.property Q.val Q.property hP hQ)
    (candidateGenusFieldGen hd) (fun P => by simp)
  -- Transport along `adjoin ℚ (range gen) = ⊤`, which is the candidate genus field itself.
  have e : adjoin ℚ (Set.range (candidateGenusFieldGen hd)) ≃ₐ[ℚ] candidateGenusField hd :=
    (IntermediateField.equivOfEq (adjoin_range_candidateGenusFieldGen_eq_top hd)).trans
      IntermediateField.topEquiv
  rw [← NumberField.discr_eq_discr_of_algEquiv _ e, h, Fintype.card_coe,
    Finset.prod_coe_sort (genusPrimeDiscriminants hd)
      (fun P => P.natAbs ^ (2 ^ ((genusPrimeDiscriminants hd).card - 1)))]

/-- **The primes ramifying in the candidate genus field are those ramifying in `ℚ(√d)`.** A
rational prime `p` is unramified in `candidateGenusField hd` exactly when it does not divide
`fundamentalDiscriminant d`, the discriminant of `ℚ(√d)`.

Both directions read off `natAbs_discr_candidateGenusField`: the prime divisors of the
discriminant of the compositum are the prime divisors of the chosen prime-discriminant factors,
and those are the prime divisors of their product `fundamentalDiscriminant d`. -/
theorem isUnramifiedIn_candidateGenusField_iff (hd : Squarefree d) {p : ℕ} (hp : p.Prime) :
    Algebra.IsUnramifiedIn (𝓞 (candidateGenusField hd)) (Ideal.span {(p : ℤ)}) ↔
      ¬ (p : ℤ) ∣ fundamentalDiscriminant d := by
  classical
  obtain ⟨-, -, hprod⟩ := genusPrimeDiscriminants_spec hd
  rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn (candidateGenusField hd)
    (𝓞 (candidateGenusField hd)) (Nat.prime_iff_prime_int.mp hp), not_iff_not, ← hprod]
  constructor
  · intro hdvd
    have hnat : p ∣ (NumberField.discr (candidateGenusField hd)).natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hdvd
    rw [natAbs_discr_candidateGenusField hd] at hnat
    obtain ⟨P, hP, hpP⟩ := hp.prime.exists_mem_finset_dvd hnat
    exact (Int.natAbs_dvd_natAbs.mp (by simpa using hp.dvd_of_dvd_pow hpP)).trans
      (Finset.dvd_prod_of_mem _ hP)
  · intro hdvd
    obtain ⟨P, hP, hpP⟩ := (Nat.prime_iff_prime_int.mp hp).exists_mem_finset_dvd hdvd
    have hnat : p ∣ (NumberField.discr (candidateGenusField hd)).natAbs := by
      rw [natAbs_discr_candidateGenusField hd]
      exact ((dvd_pow (by simpa using Int.natAbs_dvd_natAbs.mpr hpP)
        (Nat.two_pow_pos _).ne')).trans (Finset.dvd_prod_of_mem _ hP)
    exact Int.natAbs_dvd_natAbs.mp (by simpa using hnat)

end TauCeti.Multiquadratic
