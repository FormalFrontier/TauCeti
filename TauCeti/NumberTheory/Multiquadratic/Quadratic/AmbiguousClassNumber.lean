/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.TwoRank
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Ambiguous.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Ambiguous.Narrow
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.ClassGroup
import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace

/-!
# The ambiguous class number formula for a quadratic field

Let `K = ℚ(√d)` with `d` squarefree, and let `t` be the number of rational primes that ramify in
`K`. An ideal class is *ambiguous* when it is fixed by the quadratic conjugation `σ`; since `σ` acts
on `Cl(K)` by inversion, the ambiguous classes are exactly the `2`-torsion classes
(`NumberField.mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff`), and for an imaginary field
each of them is the class of an *ambiguous ideal* `I = σI`
(`NumberField.sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self`). In the narrow class
group `Cl⁺(K)` of a field of either signature, the `2`-torsion classes are likewise exactly the
narrow classes of ambiguous ideals
(`NumberField.NarrowClassGroup.sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self`). The
**ambiguous class number formula** counts them:

`#{C ∈ Cl⁺(K) | C² = 1} = 2 ^ (t - 1)`, and, for `d < 0`,
`#{C ∈ Cl(K) | σC = C} = #{C ∈ Cl(K) | C² = 1} = 2 ^ (t - 1)`.

These are the cardinality forms of the `2`-rank formulas `rank₂ Cl⁺(K) = t - 1`
(`narrowTwoRank_eq_ncard_ramifiedPrimes_sub_one`) and, for imaginary `K`, `rank₂ Cl(K) = t - 1`
(`twoRank_eq_ncard_ramifiedPrimes_sub_one`): the `2`-torsion subgroup and the maximal
elementary-`2` quotient of a finite abelian group have the same size
(`TauCeti.card_elementaryTwoQuotient_eq_card_twoTorsion`).

The formula is classical; see D. A. Cox, *Primes of the Form x² + ny²*, §3.B and §6.A, and
F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2. For a real quadratic field the
count of ambiguous classes of the *ordinary* class group also depends on the norms of the units,
and the clean formula `2 ^ (t - 1)` is a statement about the narrow class group.

## Main results

* `TauCeti.Multiquadratic.natCard_classGroup_sq_eq_one_eq_two_pow`: an imaginary quadratic field
  has exactly `2 ^ (t - 1)` ideal classes of order dividing `2`.
* `TauCeti.Multiquadratic.natCard_mulEquiv_ringOfIntegersQuadraticConj_eq_self_eq_two_pow`: the
  same count for the classes fixed by quadratic conjugation, the ambiguous classes.
* `TauCeti.Multiquadratic.natCard_exists_map_ringOfIntegersQuadraticConj_eq_self_eq_two_pow`: the
  same count for the classes of ambiguous ideals.
* `TauCeti.Multiquadratic.natCard_narrowClassGroup_sq_eq_one_eq_two_pow`: a quadratic field of
  either signature has exactly `2 ^ (t - 1)` narrow ideal classes of order dividing `2`.
* `TauCeti.Multiquadratic.natCard_narrowClassGroup_exists_map_conj_eq_self_eq_two_pow` counts the
  same narrow classes as narrow classes of ambiguous ideals.
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
  rw [← TauCeti.ClassGroup.card_elementaryTwoQuotient_eq_card_twoTorsion,
    TauCeti.ClassGroup.card_elementaryTwoQuotient_eq_two_pow_twoRank,
    twoRank_eq_ncard_ramifiedPrimes_sub_one hmin hgen hsf hd]

/-- **The ambiguous class number formula, counted by conjugation-fixed classes.** For `K = ℚ(√d)`
with `d < 0` squarefree, exactly `2 ^ (t - 1)` ideal classes are fixed by the quadratic
conjugation, where `t` is the number of rational primes ramifying in `K`. -/
theorem natCard_mulEquiv_ringOfIntegersQuadraticConj_eq_self_eq_two_pow
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : d < 0) :
    Nat.card {C : ClassGroup (𝓞 K) //
      ClassGroup.mulEquiv (ringOfIntegersQuadraticConj hmin hgen) C = C} =
      2 ^ ((ramifiedPrimes K).ncard - 1) := by
  rw [← natCard_classGroup_sq_eq_one_eq_two_pow hmin hgen hsf hd]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun C =>
    mulEquiv_ringOfIntegersQuadraticConj_apply_eq_self_iff hmin hgen C)

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

/-! ### The narrow class group, for either signature -/

/-- **The narrow ambiguous class number formula.** For `K = ℚ(√d)` with `d` squarefree and
`1 < |d|`, of either signature, the number of narrow ideal classes `C` with `C ^ 2 = 1` is
`2 ^ (t - 1)`, where `t` is the number of rational primes ramifying in `K`. -/
theorem natCard_narrowClassGroup_sq_eq_one_eq_two_pow
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 1 < d.natAbs) :
    Nat.card {C : NarrowClassGroup K // C ^ 2 = 1} = 2 ^ ((ramifiedPrimes K).ncard - 1) := by
  rw [← TauCeti.card_elementaryTwoQuotient_eq_card_twoTorsion,
    NarrowClassGroup.card_elementaryTwoQuotient_eq_two_pow_twoRank,
    narrowTwoRank_eq_ncard_ramifiedPrimes_sub_one hmin hgen hsf hd]

/-- **The narrow ambiguous class number formula, counted by ambiguous ideals.** For `K = ℚ(√d)`
with `d` squarefree and `1 < |d|`, of either signature, exactly `2 ^ (t - 1)` narrow ideal classes
are represented by an ideal fixed by the quadratic conjugation, where `t` is the number of rational
primes ramifying in `K`. -/
theorem natCard_narrowClassGroup_exists_map_conj_eq_self_eq_two_pow
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : 1 < d.natAbs) :
    Nat.card {C : NarrowClassGroup K // ∃ I : (Ideal (𝓞 K))⁰,
      Ideal.map (ringOfIntegersQuadraticConj hmin hgen) (I : Ideal (𝓞 K)) = (I : Ideal (𝓞 K)) ∧
        NarrowClassGroup.mk0 I = C} = 2 ^ ((ramifiedPrimes K).ncard - 1) := by
  rw [← natCard_narrowClassGroup_sq_eq_one_eq_two_pow hmin hgen hsf hd]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun C =>
    (NarrowClassGroup.sq_eq_one_iff_exists_map_ringOfIntegersQuadraticConj_eq_self hmin hgen
      C).symm)

end TauCeti.Multiquadratic
