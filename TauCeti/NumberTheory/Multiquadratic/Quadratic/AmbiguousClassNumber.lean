/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.TwoRank
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Ambiguous.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace

/-!
# The ambiguous class number formula for an imaginary quadratic field

Let `K = ℚ(√d)` with `d < 0` squarefree, and let `t` be the number of rational primes that ramify
in `K`. An ideal class of `K` is *ambiguous* when it is fixed by the quadratic conjugation `σ`;
since `σ` acts on `Cl(K)` by inversion, the ambiguous classes are exactly the `2`-torsion classes,
and since `K` is totally complex each of them is the class of an *ambiguous ideal* `I = σI`
(`NumberField.sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self`). The **ambiguous class
number formula** counts them:

`#{C ∈ Cl(K) | C² = 1} = 2 ^ (t - 1)`.

This is the cardinality form of the `2`-rank formula `rank₂ Cl(K) = t - 1`
(`twoRank_eq_ncard_ramifiedPrimes_sub_one`): the `2`-torsion subgroup and the maximal
elementary-`2` quotient of a finite abelian group have the same size
(`TauCeti.card_elementaryTwoQuotient_eq_card_twoTorsion`).

The formula is classical; see D. A. Cox, *Primes of the Form x² + ny²*, §3.B and §6.A, and
F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2. For a real quadratic field the
count of ambiguous classes of the ordinary class group also depends on the norms of the units, and
the clean formula `2 ^ (t - 1)` is a statement about the narrow class group.

## Main results

* `TauCeti.Multiquadratic.natCard_classGroup_sq_eq_one_eq_two_pow`: an imaginary quadratic field
  has exactly `2 ^ (t - 1)` ideal classes of order dividing `2`.
* `TauCeti.Multiquadratic.natCard_exists_map_ringOfIntegersQuadraticConj_eq_self_eq_two_pow`
  counts the same classes as classes of ambiguous ideals.
-/

public section

open Polynomial NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The ambiguous class number formula for an imaginary quadratic field.** For `K = ℚ(√d)` with
`d < 0` squarefree, the number of ideal classes `C` with `C ^ 2 = 1` is `2 ^ (t - 1)`, where `t` is
the number of rational primes ramifying in `K`. -/
theorem natCard_classGroup_sq_eq_one_eq_two_pow
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : d < 0) :
    Nat.card {C : ClassGroup (𝓞 K) // C ^ 2 = 1} = 2 ^ ((ramifiedPrimes K).ncard - 1) := by
  rw [← TauCeti.card_elementaryTwoQuotient_eq_card_twoTorsion,
    TauCeti.card_elementaryTwoQuotient_eq_two_pow_twoRank, TauCeti.twoRank_def,
    ← TauCeti.ClassGroup.twoRank_def, twoRank_eq_ncard_ramifiedPrimes_sub_one hmin hgen hsf hd]

/-- **The ambiguous class number formula, counted by ambiguous ideals.** For `K = ℚ(√d)` with
`d < 0` squarefree, exactly `2 ^ (t - 1)` ideal classes are represented by an ideal fixed by the
quadratic conjugation, where `t` is the number of rational primes ramifying in `K`. -/
theorem natCard_exists_map_ringOfIntegersQuadraticConj_eq_self_eq_two_pow
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : d < 0) :
    Nat.card {C : ClassGroup (𝓞 K) // ∃ I : (Ideal (𝓞 K))⁰,
      Ideal.map (ringOfIntegersQuadraticConj hmin hgen) (I : Ideal (𝓞 K)) = (I : Ideal (𝓞 K)) ∧
        ClassGroup.mk0 I = C} = 2 ^ ((ramifiedPrimes K).ncard - 1) := by
  have : IsTotallyComplex K := isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg hmin hd
  rw [← natCard_classGroup_sq_eq_one_eq_two_pow hmin hgen hsf hd]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun C =>
    (sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self hmin hgen C).symm)

end TauCeti.Multiquadratic
