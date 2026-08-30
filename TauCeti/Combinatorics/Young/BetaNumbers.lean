/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Beta-numbers of a Young diagram

Fix a Young diagram `μ` and a bound `r` on its number of rows. The `i`-th **beta-number**
`YoungDiagram.betaNumber μ r i = μ.rowLen i + (r - 1 - i)` is the length of row `i` plus the number
`r - 1 - i` of rows of the bounding `r`-row strip that lie below it. Adding that shift to the weakly
decreasing row lengths makes the beta-numbers strictly decrease across the indices `i < j < r`
inside the bound, so those `r` numbers are pairwise distinct; that is the whole point of the
construction, and it is all this file proves.

Beta-numbers are the bookkeeping device behind the Frobenius determinant formula and the
Frame-Robinson-Thrall route to the hook-length formula. Their relation to hook lengths --- for the
exact row count `r = μ.colLen 0` the beta-numbers of the nonempty rows `i < μ.colLen 0` are the
hook lengths of the first column, and in general they describe a row of hook lengths --- needs the
hook-length API and is developed in `TauCeti/Combinatorics/Young/HookLength/BetaNumbers.lean`.

## Main definitions

* `YoungDiagram.betaNumber`: the beta-numbers of `μ` relative to a bound `r` on its number of rows.

## Main results

* `YoungDiagram.betaNumber_lt_betaNumber`: the beta-numbers strictly decrease across the indices
  `i < j < r` inside the bound.
* `YoungDiagram.injOn_betaNumber`: the beta-numbers of the indices `i < r` are pairwise distinct.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I, Section
  1, Example 1, for beta-numbers and the description of a row of hook lengths by them.
-/

public section

namespace YoungDiagram

variable {μ : YoungDiagram} {r i j : ℕ}

/-- The `i`-th **beta-number** of a Young diagram `μ`, relative to a bound `r` on its number of
rows: the length of row `i` plus the number `r - 1 - i` of rows of the bounding `r`-row strip that
lie below it. For `r = μ.colLen 0` and a nonempty row `i < μ.colLen 0` this is the hook length of
the first cell of row `i`; see `YoungDiagram.betaNumber_eq_hookLength`. -/
def betaNumber (μ : YoungDiagram) (r i : ℕ) : ℕ := μ.rowLen i + (r - 1 - i)

theorem betaNumber_def (μ : YoungDiagram) (r i : ℕ) :
    μ.betaNumber r i = μ.rowLen i + (r - 1 - i) := (rfl)

/-- The beta-numbers strictly decrease along the rows, because the row lengths are weakly
decreasing while the shifts `r - 1 - i` strictly decrease. -/
theorem betaNumber_lt_betaNumber (μ : YoungDiagram) (hij : i < j) (hj : j < r) :
    μ.betaNumber r j < μ.betaNumber r i := by
  have := μ.rowLen_anti i j hij.le
  simp only [betaNumber_def]
  omega

-- The antecedents of `betaNumber_lt_betaNumber` mention no beta-number, so the `@[grind →]`
-- pattern does not exist; the useful trigger is a pair of beta-numbers sharing a bound, which is
-- what makes `grind` derive `βᵢ ≠ βⱼ` and `βᵢ - βⱼ ≠ 0` on its own.
grind_pattern betaNumber_lt_betaNumber => μ.betaNumber r i, μ.betaNumber r j

/-- The beta-numbers of the rows inside the bound strictly decrease. -/
theorem strictAntiOn_betaNumber (μ : YoungDiagram) (r : ℕ) :
    StrictAntiOn (μ.betaNumber r) (Set.Iio r) :=
  fun _ _ _ hb hab => μ.betaNumber_lt_betaNumber hab (Set.mem_Iio.mp hb)

/-- The beta-numbers of the rows inside the bound are pairwise distinct. -/
theorem injOn_betaNumber (μ : YoungDiagram) (r : ℕ) :
    Set.InjOn (μ.betaNumber r) (Set.Iio r) :=
  (μ.strictAntiOn_betaNumber r).injOn

end YoungDiagram
