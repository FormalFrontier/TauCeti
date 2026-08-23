/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Independence

/-!
# Degree of the candidate genus field

For a squarefree integer `d`, `candidateGenusField hd` is the compositum of the quadratic
fields attached to the prime discriminants in `genusPrimeDiscriminants hd`. This file proves
that this compositum has the full multiquadratic degree

`[candidateGenusField hd : ℚ] = 2 ^ (genusPrimeDiscriminants hd).card`.

The defining properties of `genusPrimeDiscriminants hd` say that its members are prime
discriminants and that at most one is even. Their radicands are therefore square-class
independent (`not_isSquare_prod_genusPrimeDiscriminantRadicands`), and the degree formula is the
corresponding specialization of `finrank_adjoin_range`.

This is the degree step in proving that the candidate genus field is multiquadratic. Identifying
this candidate with the maximal extension satisfying the genus-field ramification conditions is
later work.

The prime-discriminant description of the genus field is classical; see D. A. Cox,
*Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*.

## Main results

* `TauCeti.Multiquadratic.not_isSquare_prod_genusPrimeDiscriminantRadicands`: the radicands of the
  chosen prime discriminants are square-class independent.
* `TauCeti.Multiquadratic.finiteDimensional_candidateGenusField`: the candidate genus field is a
  finite extension of `ℚ`.
* `TauCeti.Multiquadratic.finrank_candidateGenusField`: its degree over `ℚ` is `2` to the number
  of prime discriminants in its chosen factorization.
* `TauCeti.Multiquadratic.adjoin_range_candidateGenusFieldGen_eq_top`: the chosen roots generate
  it: adjoining their range to `ℚ` gives all of it.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- **Square-class independence of the chosen radicands.** No nonempty subset product of the
radicands of the prime discriminants in `genusPrimeDiscriminants hd` is a rational square: the
chosen factorization consists of distinct prime discriminants, at most one of them even. -/
theorem not_isSquare_prod_genusPrimeDiscriminantRadicands {d : ℤ} (hd : Squarefree d)
    (S : Finset {P // P ∈ genusPrimeDiscriminants hd}) (hS : S.Nonempty) :
    ¬ IsSquare (∏ P ∈ S, ((primeDiscriminantRadicand P.val : ℤ) : ℚ)) := by
  obtain ⟨hprime, heven_unique, _⟩ := genusPrimeDiscriminants_spec hd
  exact not_isSquare_prod_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq
    (fun P : {P // P ∈ genusPrimeDiscriminants hd} => P.val)
    (fun P => hprime P.val P.property) Subtype.val_injective
    (fun P Q hP hQ => heven_unique P.val P.property Q.val Q.property hP hQ) S hS

/-- The candidate genus field is finite-dimensional over `ℚ`. -/
noncomputable instance finiteDimensional_candidateGenusField {d : ℤ} {hd : Squarefree d} :
    FiniteDimensional ℚ (candidateGenusField hd) := by
  rw [candidateGenusField_def]
  apply finiteDimensional_adjoin
  rintro _ ⟨P, rfl⟩
  apply IsIntegral.of_pow (by norm_num : 0 < 2)
  rw [genusFieldRoot_sq]
  exact isIntegral_algebraMap

/-- The candidate genus field is a number field: a finite extension of `ℚ` (inside `ℂ`). -/
noncomputable instance numberField_candidateGenusField {d : ℤ} {hd : Squarefree d} :
    NumberField (candidateGenusField hd) :=
  NumberField.of_module_finite ℚ (candidateGenusField hd)

/-- **Degree of the candidate genus field.** If `d` is squarefree, adjoining the chosen square
roots of the radicands of the prime discriminants in `genusPrimeDiscriminants hd` gives an
extension of `ℚ` of degree `2 ^ (genusPrimeDiscriminants hd).card`. Thus the candidate genus
field has the full degree predicted by square-class independence. -/
theorem finrank_candidateGenusField {d : ℤ} (hd : Squarefree d) :
    Module.finrank ℚ (candidateGenusField hd) =
      2 ^ (genusPrimeDiscriminants hd).card := by
  classical
  have hroot : ∀ P : {P // P ∈ genusPrimeDiscriminants hd},
      genusFieldRoot hd P ^ 2 =
        algebraMap ℚ ℂ (((primeDiscriminantRadicand P.val : ℤ) : ℚ)) := fun P => by simp
  rw [candidateGenusField_def]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    finrank_adjoin_range hroot (not_isSquare_prod_genusPrimeDiscriminantRadicands hd)

/-- The chosen roots generate the candidate genus field: adjoining their range to `ℚ` inside
`candidateGenusField hd` gives all of it. -/
theorem adjoin_range_candidateGenusFieldGen_eq_top {d : ℤ} (hd : Squarefree d) :
    adjoin ℚ (Set.range (candidateGenusFieldGen hd)) = ⊤ := by
  -- Compare the two sides through their images in `ℂ`: the generators are the chosen roots, which
  -- generate the candidate genus field by definition.
  have himage : (candidateGenusField hd).val '' Set.range (candidateGenusFieldGen hd)
      = Set.range (genusFieldRoot hd) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun P => candidateGenusFieldGen_val hd P)
  refine IntermediateField.map_injective (candidateGenusField hd).val ?_
  refine (IntermediateField.adjoin_map ℚ _ _).trans ?_
  refine Eq.trans ?_ (IntermediateField.lift_top (F := ℚ) (candidateGenusField hd)).symm
  rw [himage, candidateGenusField_def]

end TauCeti.Multiquadratic
