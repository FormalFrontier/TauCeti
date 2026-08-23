/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.TwoRank
public import TauCeti.NumberTheory.Multiquadratic.MinusFive.Basic
import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants

/-!
# The `2`-rank of the class group of `ℚ(√-5)`

Applying the genus-theoretic `2`-rank formula `2-rank Cl(K) = t - 1` to `K = ℚ(√-5)`. The
fundamental discriminant is `-20 = (-4) · 5`, a product of two prime discriminants, so `t = 2`
rational primes ramify (`2` and `5`) and the `2`-rank of the class group is `1`.

This corroborates the independently proved `NumberField.classNumber ℚ(√-5) = 2`
(`MinusFive/ClassNumber.lean`): the class group is `ℤ/2ℤ`, whose `2`-rank is indeed `1`, so genus
theory (predicting `t - 1 = 1` purely from ramification) and the direct class-number computation
agree.

## Main results

* `TauCeti.Multiquadratic.twoRank_eq_one_of_minpoly_eq_X_sq_add_five`: presentation-independent.
* `TauCeti.Multiquadratic.twoRank_adjoinRoot_sqrt_neg_five_eq_one`: on the concrete model
  `AdjoinRoot (X² + 5)`.
-/

public section

open Polynomial NumberField
open scoped NumberField

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- **The `2`-rank of the class group of `ℚ(√-5)` is `1`.** Its fundamental discriminant `-20`
factors as `(-4) · 5` into two prime discriminants, so two rational primes ramify (`t = 2`) and
`2-rank Cl = t - 1 = 1`. This corroborates `NumberField.classNumber ℚ(√-5) = 2` (`Cl ≅ ℤ/2ℤ`). -/
theorem twoRank_eq_one_of_minpoly_eq_X_sq_add_five
    (hmin : minpoly ℤ θ = X ^ 2 - C (-5 : ℤ)) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    TauCeti.ClassGroup.twoRank (𝓞 K) = 1 := by
  have hsf : Squarefree (-5 : ℤ) := (Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree
  have hs : ∀ P ∈ ({-4, 5} : Finset ℤ), IsPrimeDiscriminant P := by
    intro P hP
    fin_cases hP
    · exact isPrimeDiscriminant_neg_four
    · simpa [oddPrimeDiscriminant_of_mod_four_eq_one (by norm_num : 5 % 4 = 1)]
        using isPrimeDiscriminant_oddPrimeDiscriminant (p := 5) (by decide) (by decide)
  have heven : ∀ P ∈ ({-4, 5} : Finset ℤ), ∀ Q ∈ ({-4, 5} : Finset ℤ),
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q := by
    intro P hP Q hQ
    fin_cases hP <;> fin_cases hQ <;> simp only [IsEvenPrimeDiscriminant] <;> decide
  have hprod : ∏ P ∈ ({-4, 5} : Finset ℤ), P = fundamentalDiscriminant (-5 : ℤ) := by
    rw [Finset.prod_insert (by decide : (-4 : ℤ) ∉ ({5} : Finset ℤ)), Finset.prod_singleton,
      fundamentalDiscriminant_of_mod_four_ne_one (by decide : (-5 : ℤ) % 4 ≠ 1)]
    ring
  have hncard : (ramifiedPrimes K).ncard = 2 := by
    rw [ncard_ramifiedPrimes_eq_card hmin hgen hsf hs heven hprod,
      Finset.card_pair (show (-4 : ℤ) ≠ 5 by decide)]
  rw [twoRank_eq_ncard_ramifiedPrimes_sub_one hmin hgen hsf (by norm_num), hncard]

/-- **Worked example.** The concrete number field `AdjoinRoot (X² + 5)`, modelling `ℚ(√-5)`, has
class-group `2`-rank `1`. Not `@[simp]`: the `@[simp]` lemma `twoRank_def` unfolds the left-hand
side `twoRank _`, so this closed form is not in simp-normal form (`simpNF` rejects it), unlike the
non-unfolded `classNumber` companion. -/
theorem twoRank_adjoinRoot_sqrt_neg_five_eq_one :
    TauCeti.ClassGroup.twoRank (𝓞 (AdjoinRoot (X ^ 2 - C (-5 : ℚ)))) = 1 := by
  obtain ⟨θ, hmin, hgen⟩ := NumberField.exists_minpoly_eq_X_sq_add_five_and_adjoin_eq_top
  exact twoRank_eq_one_of_minpoly_eq_X_sq_add_five hmin hgen

end TauCeti.Multiquadratic
