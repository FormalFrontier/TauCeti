/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Examples.Lists
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.GaloisGroup

/-!
# The `ℚ(√-21)` genus-field worked example

The multiquadratic roadmap's genus-field worked example identifies the genus field of `ℚ(√-21)`
as `ℚ(√-1, √-3, √-7)`, attached to the prime-discriminant list `[-4, -3, -7]` (recorded, with its
arithmetic witnesses, in `TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Examples.Lists`).
This file collects the Layer-0 field-theoretic content of that example: the concrete complex roots
`i`, `i√3`, `i√7` and their squaring lemmas, the degree `[ℚ(i, √-3, √-7) : ℚ] = 8`, and the
Galois-group cardinality `|Gal(ℚ(i, √-3, √-7)/ℚ)| = 8`.

Both the degree and the Galois-group readings are instances of the field-generic
prime-discriminant packages `TauCeti.Multiquadratic.finrank_adjoin_roots_primeDiscriminantRadicands`
and `TauCeti.Multiquadratic.card_aut_adjoin_roots_primeDiscriminantRadicands`, fed the arithmetic
witnesses for `[-4, -3, -7]` and the square roots supplied here. The purely integer-valued
Legendre-character criteria for the same list live in
`TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Examples`; keeping them there means
the character-theory layer, and the complete-splitting example that consumes it, need not depend on
`Complex`/`Real.sqrt`.

The prime-discriminant convention follows Cox's *Primes of the Form x² + ny²* and Lemmermeyer's
*Reciprocity Laws*.

## Main results

* `TauCeti.Multiquadratic.finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven`:
  `[ℚ(i, √-3, √-7) : ℚ] = 8`.
* `TauCeti.Multiquadratic.card_aut_adjoin_I_sqrt_neg_three_sqrt_neg_seven`:
  `|Gal(ℚ(i, √-3, √-7)/ℚ)| = 8`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

/-- The complex number `i√n` squares to `-n`. -/
private theorem I_mul_real_sqrt_nat_sq (n : ℕ) :
    (Complex.I * ((Real.sqrt n : ℝ) : ℂ)) ^ 2 = -(n : ℂ) := by
  have hsqrt : (((Real.sqrt n : ℝ) : ℂ) ^ 2) = (n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
  calc
    (Complex.I * ((Real.sqrt n : ℝ) : ℂ)) ^ 2 =
        Complex.I ^ 2 * (((Real.sqrt n : ℝ) : ℂ) ^ 2) := by
      ring
    _ = -(n : ℂ) := by
      simp [Complex.I_sq, hsqrt]

/-- The chosen complex square root of `-3`, namely `i√3`. -/
noncomputable abbrev sqrtNegThree : ℂ :=
  Complex.I * ((Real.sqrt 3 : ℝ) : ℂ)

/-- The chosen root `sqrtNegThree` squares to `-3`. -/
@[simp]
theorem sqrtNegThree_sq : sqrtNegThree ^ 2 = (-3 : ℂ) := by
  simpa [sqrtNegThree] using I_mul_real_sqrt_nat_sq 3

/-- The chosen complex square root of `-7`, namely `i√7`. -/
noncomputable abbrev sqrtNegSeven : ℂ :=
  Complex.I * ((Real.sqrt 7 : ℝ) : ℂ)

/-- The chosen root `sqrtNegSeven` squares to `-7`. -/
@[simp]
theorem sqrtNegSeven_sq : sqrtNegSeven ^ 2 = (-7 : ℂ) := by
  simpa [sqrtNegSeven] using I_mul_real_sqrt_nat_sq 7

/-- The three radicands `-1`, `-3`, and `-7` associated to the prime discriminants in
the `ℚ(√-21)` genus-field example. -/
def minusTwentyOneRadicand : Fin 3 → ℚ :=
  ![-1, -3, -7]

/-- Chosen complex roots `i`, `i√3`, and `i√7` of the radicands in the
`ℚ(√-21)` genus-field example. -/
noncomputable def minusTwentyOneRoot : Fin 3 → ℂ :=
  ![Complex.I, sqrtNegThree, sqrtNegSeven]

@[simp] theorem minusTwentyOneRadicand_zero : minusTwentyOneRadicand 0 = -1 := (rfl)

@[simp] theorem minusTwentyOneRadicand_one : minusTwentyOneRadicand 1 = -3 := (rfl)

@[simp] theorem minusTwentyOneRadicand_two : minusTwentyOneRadicand 2 = -7 := (rfl)

@[simp] theorem minusTwentyOneRoot_zero : minusTwentyOneRoot 0 = Complex.I := (rfl)

@[simp] theorem minusTwentyOneRoot_one : minusTwentyOneRoot 1 = sqrtNegThree := (rfl)

@[simp] theorem minusTwentyOneRoot_two : minusTwentyOneRoot 2 = sqrtNegSeven := (rfl)

/-- The radicands for the `ℚ(√-21)` example agree with those associated to its three
prime discriminants. -/
theorem minusTwentyOneRadicand_eq_primeDiscriminantRadicand (i : Fin 3) :
    minusTwentyOneRadicand i =
      ((primeDiscriminantRadicand
        (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ) := by
  fin_cases i <;> simp [negFourNegThreeNegSevenPrimeDiscriminants,
    primeDiscriminantRadicand]

/-- Each chosen root for the `ℚ(√-21)` example squares to its corresponding radicand. -/
theorem minusTwentyOneRoot_sq (i : Fin 3) :
    minusTwentyOneRoot i ^ 2 = algebraMap ℚ ℂ (minusTwentyOneRadicand i) := by
  fin_cases i
  · simp [Complex.I_sq]
  · simp
  · simp

/-- The complex square root data for the prime discriminants `-4`, `-3`, and `-7`: the
associated radicands are `-1`, `-3`, and `-7`, with roots `i`, `i√3`, and `i√7`. -/
private theorem root_neg_four_neg_three_neg_seven_sq (i : Fin 3) :
    minusTwentyOneRoot i ^ 2 =
      algebraMap ℚ ℂ
        (((primeDiscriminantRadicand
          (negFourNegThreeNegSevenPrimeDiscriminants i) : ℤ) : ℚ)) := by
  rw [← minusTwentyOneRadicand_eq_primeDiscriminantRadicand]
  exact minusTwentyOneRoot_sq i

/-- The range of the chosen prime-discriminant root family for the `ℚ(√-21)` example is
`{i, √-3, √-7}`. -/
private theorem range_roots_neg_four_neg_three_neg_seven :
    Set.range minusTwentyOneRoot
      = {Complex.I, sqrtNegThree, sqrtNegSeven} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [hx]⟩
    · exact ⟨2, by simp [hx]⟩

/-- **Worked example: `[ℚ(i, √-3, √-7) : ℚ] = 8`.** This is the Layer-0 degree statement for
the multiquadratic field generated by the prime-discriminant radicands `-1`, `-3`, and `-7`,
the genus-field generator list for `ℚ(√-21)`. -/
theorem finrank_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Module.finrank ℚ
      (adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) : IntermediateField ℚ ℂ)
      = 8 := by
  have h := finrank_adjoin_roots_primeDiscriminantRadicands
    negFourNegThreeNegSevenPrimeDiscriminants
    isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants
    injective_negFourNegThreeNegSevenPrimeDiscriminants
    not_all_three_evenPrimeDiscriminants_negFourNegThreeNegSevenPrimeDiscriminants
    minusTwentyOneRoot
    root_neg_four_neg_three_neg_seven_sq
  rw [range_roots_neg_four_neg_three_neg_seven] at h
  exact h.trans (by norm_num [Nat.card_fin])

/-- **Worked example: `|Gal(ℚ(i, √-3, √-7)/ℚ)| = 8`.** This is the Galois group of the
multiquadratic field `ℚ(√-1, √-3, √-7)` attached to the prime discriminants `-4`, `-3`,
and `-7` in the genus-field example for `ℚ(√-21)`. -/
theorem card_aut_adjoin_I_sqrt_neg_three_sqrt_neg_seven :
    Nat.card
      ((adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
          IntermediateField ℚ ℂ)
          ≃ₐ[ℚ]
        (adjoin ℚ ({Complex.I, sqrtNegThree, sqrtNegSeven} : Set ℂ) :
          IntermediateField ℚ ℂ))
      = 8 := by
  have h := card_aut_adjoin_roots_primeDiscriminantRadicands
    negFourNegThreeNegSevenPrimeDiscriminants
    isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants
    injective_negFourNegThreeNegSevenPrimeDiscriminants
    not_all_three_evenPrimeDiscriminants_negFourNegThreeNegSevenPrimeDiscriminants
    minusTwentyOneRoot
    root_neg_four_neg_three_neg_seven_sq
  rw [← range_roots_neg_four_neg_three_neg_seven]
  exact h.trans (by norm_num [Nat.card_fin])

end TauCeti.Multiquadratic
