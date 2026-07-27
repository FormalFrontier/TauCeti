/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Worked examples of fundamental discriminants

The multiquadratic roadmap's `Worked examples` section (`TauCetiRoadmap/Multiquadratic/README.md`)
lists `ℚ(√-5)`, with discriminant `-20` and genus field `ℚ(√-1, √5)`, and `ℚ(√-21)`, with
discriminant `-84` and genus field `ℚ(√-1, √-3, √-7)`. This file establishes the
fundamental-discriminant component of those examples: each discriminant is derived as a product
of prime discriminants through
`isFundamentalDiscriminant_mul_prod_oddPrimeDiscriminant_of_isEvenPrimeDiscriminant`, rather than
by unfolding the definition. The class-group and genus-field claims remain for later work.

## Main results

* `TauCeti.Multiquadratic.isFundamentalDiscriminant_neg_twenty`: `-20` is a fundamental
  discriminant.
* `TauCeti.Multiquadratic.isFundamentalDiscriminant_neg_eighty_four`: `-84` is a fundamental
  discriminant.
-/

public section

namespace TauCeti.Multiquadratic

/-- **Worked example.** `-20`, the discriminant of `ℚ(√-5)`, is a fundamental discriminant: it is
the product of the prime discriminants `-4` and `5`, whose square roots generate the genus field
`ℚ(√-1, √5)`. -/
theorem isFundamentalDiscriminant_neg_twenty : IsFundamentalDiscriminant (-20) := by
  have h := isFundamentalDiscriminant_mul_prod_oddPrimeDiscriminant_of_isEvenPrimeDiscriminant
    isEvenPrimeDiscriminant_neg_four (s := ({5} : Finset ℕ)) (p := id)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst hi; norm_num)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst hi; exact Nat.odd_iff.mpr rfl)
    (by simp)
  have h5 : oddPrimeDiscriminant 5 = 5 := oddPrimeDiscriminant_of_mod_four_eq_one (by norm_num)
  have hval : (-4 : ℤ) * ∏ i ∈ ({5} : Finset ℕ), oddPrimeDiscriminant (id i) = -20 := by
    rw [Finset.prod_singleton, id_eq, h5]; norm_num
  rwa [hval] at h

/-- **Worked example.** `-84`, the discriminant of `ℚ(√-21)`, is a fundamental discriminant: it is
the product of the prime discriminants `-4`, `-3` and `-7`, whose square roots generate the genus
field `ℚ(√-1, √-3, √-7)`. -/
theorem isFundamentalDiscriminant_neg_eighty_four : IsFundamentalDiscriminant (-84) := by
  have h := isFundamentalDiscriminant_mul_prod_oddPrimeDiscriminant_of_isEvenPrimeDiscriminant
    isEvenPrimeDiscriminant_neg_four (s := ({3, 7} : Finset ℕ)) (p := id)
    (by intro i hi; fin_cases hi <;> norm_num)
    (by intro i hi; fin_cases hi <;> exact Nat.odd_iff.mpr rfl)
    (by intro i hi j hj hij; simpa using hij)
  have h3 : oddPrimeDiscriminant 3 = -3 := oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num)
  have h7 : oddPrimeDiscriminant 7 = -7 := oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num)
  have hval : (-4 : ℤ) * ∏ i ∈ ({3, 7} : Finset ℕ), oddPrimeDiscriminant (id i) = -84 := by
    rw [Finset.prod_pair (by norm_num : (3 : ℕ) ≠ 7), id_eq, id_eq, h3, h7]; norm_num
  rwa [hval] at h

end TauCeti.Multiquadratic
