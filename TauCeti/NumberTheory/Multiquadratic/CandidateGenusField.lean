/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.GenusField
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Factorization
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The candidate genus field of `ℚ(√d)`

For a squarefree integer `d`, the *candidate genus field* of `ℚ(√d)` is the compositum over `ℚ` of
the quadratic fields `ℚ(√(radicand P))` attached to the prime discriminants `P` dividing the
fundamental discriminant `fundamentalDiscriminant d`. Classically this is the genus field of
`ℚ(√d)`; identifying it with the maximal unramified abelian extension is later work.

This file gives the object a name. `GenusField` proved the underlying square-class facts for an
arbitrary finite set of prime discriminants with chosen roots; here we pin a canonical choice —
the factorization finset `genusPrimeDiscriminants` from
`IsFundamentalDiscriminant.exists_finset_primeDiscriminant`, and canonical complex roots
`genusFieldRoot` of the radicands (using that `ℂ` is algebraically closed) — and package the
compositum as `candidateGenusField`. As a first property we record that it contains a square root
of `d`, so it really is a candidate genus field *of `ℚ(√d)`*.

The prime-discriminant description is classical; see D. A. Cox, *Primes of the Form x² + ny²*, and
F. Lemmermeyer, *Reciprocity Laws*.

## Main definitions

* `TauCeti.Multiquadratic.candidateGenusField`: the candidate genus field of `ℚ(√d)`, as an
  intermediate field of `ℂ / ℚ`.

## Main results

* `TauCeti.Multiquadratic.exists_mem_candidateGenusField_sq_eq`: the candidate genus field contains
  an element squaring to `d`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- The chosen prime-discriminant factorization of `fundamentalDiscriminant d`: for squarefree `d`,
the finite set of prime discriminants dividing the discriminant of `ℚ(√d)`, from
`IsFundamentalDiscriminant.exists_finset_primeDiscriminant`. -/
noncomputable def genusPrimeDiscriminants {d : ℤ} (hd : Squarefree d) : Finset ℤ :=
  (isFundamentalDiscriminant_fundamentalDiscriminant hd).exists_finset_primeDiscriminant.choose

/-- The defining properties of `genusPrimeDiscriminants`: its members are prime discriminants, at
most one of which is even, and their product is `fundamentalDiscriminant d`. -/
theorem genusPrimeDiscriminants_spec {d : ℤ} (hd : Squarefree d) :
    (∀ P ∈ genusPrimeDiscriminants hd, IsPrimeDiscriminant P) ∧
      (∀ P ∈ genusPrimeDiscriminants hd, ∀ Q ∈ genusPrimeDiscriminants hd,
        IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q) ∧
      ∏ P ∈ genusPrimeDiscriminants hd, P = fundamentalDiscriminant d :=
  (isFundamentalDiscriminant_fundamentalDiscriminant hd).exists_finset_primeDiscriminant.choose_spec

/-- A chosen complex square root of the radicand of each prime discriminant in
`genusPrimeDiscriminants hd` (available since `ℂ` is algebraically closed). -/
noncomputable def genusFieldRoot {d : ℤ} (hd : Squarefree d)
    (P : {P // P ∈ genusPrimeDiscriminants hd}) : ℂ :=
  (IsAlgClosed.exists_pow_nat_eq ((primeDiscriminantRadicand P.val : ℤ) : ℂ) (n := 2)
    (by norm_num)).choose

/-- Each `genusFieldRoot` squares to its radicand. -/
theorem genusFieldRoot_sq {d : ℤ} (hd : Squarefree d)
    (P : {P // P ∈ genusPrimeDiscriminants hd}) :
    genusFieldRoot hd P ^ 2 = algebraMap ℚ ℂ ((primeDiscriminantRadicand P.val : ℤ) : ℚ) := by
  have h : genusFieldRoot hd P ^ 2 = ((primeDiscriminantRadicand P.val : ℤ) : ℂ) :=
    (IsAlgClosed.exists_pow_nat_eq ((primeDiscriminantRadicand P.val : ℤ) : ℂ) (n := 2)
      (by norm_num)).choose_spec
  rw [h]
  simp

/-- **The candidate genus field of `ℚ(√d)`.** For squarefree `d`, the compositum over `ℚ` of the
chosen complex square roots of the radicands of the prime discriminants dividing
`fundamentalDiscriminant d`. Classically this is the genus field of `ℚ(√d)`; identifying it with the
maximal unramified abelian extension is later work. -/
noncomputable def candidateGenusField {d : ℤ} (hd : Squarefree d) : IntermediateField ℚ ℂ :=
  adjoin ℚ (Set.range (genusFieldRoot hd))

/-- **The candidate genus field of `ℚ(√d)` contains a square root of `d`.** This is what makes it a
candidate genus field *of `ℚ(√d)`*; it specializes the square-class containment of `GenusField` to
the canonical factorization and roots. -/
theorem exists_mem_candidateGenusField_sq_eq {d : ℤ} (hd : Squarefree d) :
    ∃ x ∈ candidateGenusField hd, x ^ 2 = algebraMap ℚ ℂ ((d : ℤ) : ℚ) := by
  obtain ⟨hs, _, hprod⟩ := genusPrimeDiscriminants_spec hd
  exact exists_mem_adjoin_sq_eq_of_prod_primeDiscriminant_eq hs hprod
    (genusFieldRoot hd) (genusFieldRoot_sq hd)

end TauCeti.Multiquadratic
