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

For a squarefree integer `d`, the *candidate genus field* of `ℚ(√d)` built here is the compositum
over `ℚ` of the quadratic fields `ℚ(√(radicand P))` attached to the prime discriminants `P` dividing
the fundamental discriminant `fundamentalDiscriminant d`. This compositum is unramified at the
*finite* places. For imaginary `d`, where the narrow and ordinary genus fields coincide, it is the
genus field of `ℚ(√d)`. For real `d` it is only the *narrow* candidate and may ramify at the
infinite places: e.g. `d = 3` has `disc = 12 = (-4)·(-3)`, so the compositum is `ℚ(i, √3)`, ramified
at the real places over `ℚ(√3)`. Identifying it with the genus field unramified at *all* places —
the ordinary one for real `d`, which needs the infinite-place condition — is later work.

This file gives the object a name. `GenusField` proved the underlying square-class facts for an
arbitrary finite set of prime discriminants with chosen roots; here we fix a choice — the
factorization finset `genusPrimeDiscriminants` from
`IsFundamentalDiscriminant.exists_finset_primeDiscriminant`, and chosen complex roots
`genusFieldRoot` of the radicands (using that `ℂ` is algebraically closed) — and package the
compositum as `candidateGenusField`. (Both choices are made with `choose`; independence of the
resulting field from them is not claimed here.) As a first property we record that it contains a
square root of `d`, so it really is a candidate genus field *of `ℚ(√d)`*.

The prime-discriminant description is classical; see D. A. Cox, *Primes of the Form x² + ny²*, and
F. Lemmermeyer, *Reciprocity Laws*.

## Main definitions

* `TauCeti.Multiquadratic.candidateGenusField`: the candidate genus field of `ℚ(√d)`, as an
  intermediate field of `ℂ / ℚ`.

## Main results

* `TauCeti.Multiquadratic.candidateGenusField_le_iff`: its universal property — it is below an
  intermediate field iff that field contains every chosen root.
* `TauCeti.Multiquadratic.exists_mem_candidateGenusField_sq_eq`: it contains an element squaring
  to `d`.
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

/-- Each `genusFieldRoot` squares to its radicand (in `ℂ`-cast normal form). -/
@[simp] theorem genusFieldRoot_sq {d : ℤ} (hd : Squarefree d)
    (P : {P // P ∈ genusPrimeDiscriminants hd}) :
    genusFieldRoot hd P ^ 2 = ((primeDiscriminantRadicand P.val : ℤ) : ℂ) := by
  simp only [genusFieldRoot]
  exact (IsAlgClosed.exists_pow_nat_eq _ (n := 2) (by norm_num)).choose_spec

/-- **The candidate genus field of `ℚ(√d)`.** For squarefree `d`, the compositum over `ℚ` of the
chosen complex square roots of the radicands of the prime discriminants dividing
`fundamentalDiscriminant d`. Unramified at the finite places, it is the genus field of `ℚ(√d)` for
imaginary `d` and only the narrow candidate for real `d`; identifying it with the genus field
unramified at all places (the infinite ones included) is later work. -/
noncomputable def candidateGenusField {d : ℤ} (hd : Squarefree d) : IntermediateField ℚ ℂ :=
  adjoin ℚ (Set.range (genusFieldRoot hd))

/-- `candidateGenusField` presented as the `adjoin` of its chosen roots. -/
theorem candidateGenusField_def {d : ℤ} (hd : Squarefree d) :
    candidateGenusField hd = adjoin ℚ (Set.range (genusFieldRoot hd)) := by
  simp only [candidateGenusField]

/-- Each chosen root lies in the candidate genus field. -/
@[simp] theorem genusFieldRoot_mem_candidateGenusField {d : ℤ} (hd : Squarefree d)
    (P : {P // P ∈ genusPrimeDiscriminants hd}) :
    genusFieldRoot hd P ∈ candidateGenusField hd := by
  rw [candidateGenusField_def]
  exact subset_adjoin ℚ _ ⟨P, rfl⟩

/-- **Universal property of the candidate genus field.** It is contained in an intermediate field
`F` exactly when `F` contains every chosen root. -/
theorem candidateGenusField_le_iff {d : ℤ} (hd : Squarefree d) {F : IntermediateField ℚ ℂ} :
    candidateGenusField hd ≤ F ↔ ∀ P, genusFieldRoot hd P ∈ F := by
  simp only [candidateGenusField_def, adjoin_le_iff, Set.range_subset_iff, SetLike.mem_coe]

/-- **The candidate genus field of `ℚ(√d)` contains a square root of `d`.** This is what makes it a
candidate genus field *of `ℚ(√d)`*; it specializes the square-class containment of `GenusField` to
the chosen factorization and roots. -/
theorem exists_mem_candidateGenusField_sq_eq {d : ℤ} (hd : Squarefree d) :
    ∃ x ∈ candidateGenusField hd, x ^ 2 = algebraMap ℚ ℂ ((d : ℤ) : ℚ) := by
  obtain ⟨hs, _, hprod⟩ := genusPrimeDiscriminants_spec hd
  simpa only [candidateGenusField] using
    exists_mem_adjoin_sq_eq_of_prod_primeDiscriminant_eq hs hprod (genusFieldRoot hd)
      (fun P => by simp)

end TauCeti.Multiquadratic
