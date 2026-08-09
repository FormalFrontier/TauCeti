/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.ElementaryTwoQuotient
public import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace

/-!
# Narrow class groups of number fields containing an imaginary quadratic element

If a number field `K` contains an algebraic integer `θ` with `minpoly ℤ θ = X² - d` for `d < 0`,
then it contains an imaginary quadratic subfield and has no real infinite places. Thus the totally
positive condition on generators is vacuous and the narrow class group coincides with the ordinary
one. This file records the two consequences that genus theory uses: the narrow class number is the
class number, and the narrow `2`-rank is the ordinary `2`-rank.

This is why the genus-theory `2`-rank formula `t - 1` can be stated for `Cl(K)` in the imaginary
case — the case the roadmap asks to settle first — whereas the real case genuinely needs the narrow
class group `Cl⁺(K)`, whose ordinary quotient can be smaller (`ℚ(√3)` has `t = 2` ramified primes
and class number `1`).

## Main results

* `TauCeti.NumberField.card_narrowClassGroup_eq_classNumber_of_minpoly_eq_X_sq_sub_C_of_neg`.
* `TauCeti.NumberField.twoRank_narrowClassGroup_eq_of_minpoly_eq_X_sq_sub_C_of_neg`.
-/

public section

open Polynomial NumberField
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The narrow class number of a number field containing an imaginary quadratic element is its
class number.** An element with minimal polynomial `X² - d` for `d < 0` makes the field totally
complex, so no positivity condition survives. -/
theorem card_narrowClassGroup_eq_classNumber_of_minpoly_eq_X_sq_sub_C_of_neg
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd : d < 0) :
    Nat.card (NarrowClassGroup K) = NumberField.classNumber K :=
  haveI := isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg hmin hd
  NarrowClassGroup.card_eq_classNumber

/-- **The narrow and ordinary `2`-ranks of a number field containing an imaginary quadratic element
agree.** An element with minimal polynomial `X² - d` for `d < 0` makes the field totally complex,
so the genus-theory `2`-rank may be computed with either class group. -/
theorem twoRank_narrowClassGroup_eq_of_minpoly_eq_X_sq_sub_C_of_neg
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd : d < 0) :
    NarrowClassGroup.twoRank K = TauCeti.ClassGroup.twoRank (𝓞 K) :=
  haveI := isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg hmin hd
  NarrowClassGroup.twoRank_eq_twoRank_classGroup

end TauCeti.NumberField
