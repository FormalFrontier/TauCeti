/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.TwoRank
public import TauCeti.NumberTheory.Multiquadratic.MinusTwentyOne.Basic
import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants

/-!
# The `2`-rank of the class group of `ℚ(√-21)`

Applying the genus-theoretic `2`-rank formula `2-rank Cl(K) = t - 1` to `K = ℚ(√-21)`. The
fundamental discriminant is `-84 = (-4) · (-3) · (-7)`, a product of three prime discriminants, so
`t = 3` rational primes ramify (`2`, `3` and `7`) and the `2`-rank of the class group is `2`.

Combined with `NumberField.classNumber ℚ(√-21) = 4` (`MinusTwentyOne/ClassNumber.lean`), this pins
down the group structure: a group of order `4` and `2`-rank `2` is `(ℤ/2ℤ)²`, so `Cl ≅ (ℤ/2ℤ)²`.
This is not an independent check — that class-number proof itself uses the ramified-prime lower
bound `ncard_ramifiedPrimes_sub_one_le_twoRank` to get divisibility by `4`.

## Main results

* `TauCeti.Multiquadratic.twoRank_eq_two_of_minpoly_eq_X_sq_add_twenty_one`: the
  presentation-independent statement.
* `TauCeti.Multiquadratic.twoRank_adjoinRoot_sqrt_neg_twenty_one_eq_two`: on the concrete model
  `AdjoinRoot (X² + 21)`.
-/

public section

open Polynomial NumberField
open scoped NumberField

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- **The `2`-rank of the class group of `ℚ(√-21)` is `2`.** Its fundamental discriminant `-84`
factors as `(-4) · (-3) · (-7)` into three prime discriminants, so three rational primes ramify
(`t = 3`) and `2-rank Cl = t - 1 = 2`. With `NumberField.classNumber ℚ(√-21) = 4` this pins down
`Cl ≅ (ℤ/2ℤ)²`. -/
theorem twoRank_eq_two_of_minpoly_eq_X_sq_add_twenty_one
    (hmin : minpoly ℤ θ = X ^ 2 - C (-21 : ℤ)) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    TauCeti.ClassGroup.twoRank (𝓞 K) = 2 := by
  have hsf : Squarefree (-21 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    simpa using (Nat.squarefree_mul (by decide : Nat.Coprime 3 7)).mpr
      ⟨(by decide : Nat.Prime 3).squarefree, (by decide : Nat.Prime 7).squarefree⟩
  have hs : ∀ P ∈ ({-4, -3, -7} : Finset ℤ), IsPrimeDiscriminant P := by
    intro P hP
    fin_cases hP
    · exact isPrimeDiscriminant_neg_four
    · simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 3 % 4 = 3)]
        using isPrimeDiscriminant_oddPrimeDiscriminant (p := 3) (by decide) (by decide)
    · simpa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num : 7 % 4 = 3)]
        using isPrimeDiscriminant_oddPrimeDiscriminant (p := 7) (by decide) (by decide)
  have heven : ∀ P ∈ ({-4, -3, -7} : Finset ℤ), ∀ Q ∈ ({-4, -3, -7} : Finset ℤ),
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q := by
    intro P hP Q hQ
    fin_cases hP <;> fin_cases hQ <;> simp only [IsEvenPrimeDiscriminant] <;> decide
  have hprod : ∏ P ∈ ({-4, -3, -7} : Finset ℤ), P = fundamentalDiscriminant (-21 : ℤ) := by
    rw [Finset.prod_insert (by decide : (-4 : ℤ) ∉ ({-3, -7} : Finset ℤ)),
      Finset.prod_insert (by decide : (-3 : ℤ) ∉ ({-7} : Finset ℤ)), Finset.prod_singleton,
      fundamentalDiscriminant_of_mod_four_ne_one (by decide : (-21 : ℤ) % 4 ≠ 1)]
    ring
  have hncard : (ramifiedPrimes K).ncard = 3 := by
    rw [ncard_ramifiedPrimes_eq_card hmin hgen hsf hs heven hprod,
      Finset.card_insert_of_notMem (by decide : (-4 : ℤ) ∉ ({-3, -7} : Finset ℤ)),
      Finset.card_insert_of_notMem (by decide : (-3 : ℤ) ∉ ({-7} : Finset ℤ)),
      Finset.card_singleton]
  rw [twoRank_eq_ncard_ramifiedPrimes_sub_one hmin hgen hsf (by norm_num), hncard]

/-- **Worked example.** The concrete number field `AdjoinRoot (X² + 21)`, modelling `ℚ(√-21)`, has
class-group `2`-rank `2`. Not `@[simp]`: the `@[simp]` lemma `twoRank_def` unfolds the left-hand
side `twoRank _`, so this closed form is not in simp-normal form (`simpNF` rejects it), unlike the
non-unfolded `classNumber` companion. -/
theorem twoRank_adjoinRoot_sqrt_neg_twenty_one_eq_two :
    TauCeti.ClassGroup.twoRank (𝓞 (AdjoinRoot (X ^ 2 - C (-21 : ℚ)))) = 2 := by
  obtain ⟨θ, hmin, hgen⟩ := NumberField.exists_minpoly_eq_X_sq_add_twenty_one_and_adjoin_eq_top
  exact twoRank_eq_two_of_minpoly_eq_X_sq_add_twenty_one hmin hgen

end TauCeti.Multiquadratic
