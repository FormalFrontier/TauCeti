/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants

/-!
# Prime-discriminant lists for the first genus-field examples

The multiquadratic roadmap's genus-field worked examples use the prime-discriminant lists
`[-4, 5]` for `ℚ(√-5)` and `[-4, -3, -7]` for `ℚ(√-21)`. This file gives those shared lists
a neutral home for the Legendre-character, degree, and Galois worked examples, together with
the arithmetic witness bundle (prime-discriminant, injectivity, and parity facts) for the
`[-4, -3, -7]` list reused by the `ℚ(√-21)` degree and Galois examples. The complex square
root witnesses those degree and Galois examples also need, together with the degree and
Galois worked examples themselves, live in
`TauCeti.NumberTheory.Multiquadratic.MinusTwentyOne.Examples`, so the purely
integer-valued Legendre-character examples do not depend on `Complex`/`Real.sqrt`.
-/

public section

namespace TauCeti.Multiquadratic

/-- The prime-discriminant list `[-4, 5]` for the genus-field generators of `ℚ(√-5)`. -/
abbrev negFourFivePrimeDiscriminants : Fin 2 → ℤ :=
  ![(-4 : ℤ), 5]

/-- The prime-discriminant list `[-4, -3, -7]` for the genus-field generators of
`ℚ(√-21)`. -/
abbrev negFourNegThreeNegSevenPrimeDiscriminants : Fin 3 → ℤ :=
  ![(-4 : ℤ), -3, -7]

/-- Each entry of the `[-4, -3, -7]` list is a prime discriminant. -/
theorem isPrimeDiscriminant_negFourNegThreeNegSevenPrimeDiscriminants :
    ∀ i : Fin 3, IsPrimeDiscriminant (negFourNegThreeNegSevenPrimeDiscriminants i) := by
  intro i
  fin_cases i
  · simp [negFourNegThreeNegSevenPrimeDiscriminants]
  · have h3 : IsPrimeDiscriminant (oddPrimeDiscriminant 3) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 3) (by decide) (by decide)
    simpa [negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)] using h3
  · have h7 : IsPrimeDiscriminant (oddPrimeDiscriminant 7) :=
      isPrimeDiscriminant_oddPrimeDiscriminant (p := 7) (by decide) (by decide)
    simpa [negFourNegThreeNegSevenPrimeDiscriminants,
      oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)] using h7

/-- The `[-4, -3, -7]` list has no repeated entries. -/
theorem injective_negFourNegThreeNegSevenPrimeDiscriminants :
    Function.Injective negFourNegThreeNegSevenPrimeDiscriminants := by
  decide

/-- The `[-4, -3, -7]` list does not contain all three even prime discriminants. -/
theorem not_all_three_evenPrimeDiscriminants_negFourNegThreeNegSevenPrimeDiscriminants :
    ¬ ((∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -4) ∧
      (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = 8) ∧
        (∃ i : Fin 3, negFourNegThreeNegSevenPrimeDiscriminants i = -8)) := by
  decide

end TauCeti.Multiquadratic
