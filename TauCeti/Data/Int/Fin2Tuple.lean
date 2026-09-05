/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Int.GCD

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Two-entry integer tuples

Arithmetic of `Fin 2 → ℤ`. Nothing here involves matrices; the results are stated for tuples
so that callers holding a diagonal, a pair of invariant factors, or any other two integers can
use them without dragging in linear algebra.

## Main results

* `Int.eq_of_dvd_of_dvd_of_mul_eq_mul`: two tuples with positive, mutually dividing first
  entries and equal products are equal.
-/

namespace Int

public section

/-- **Two `Fin 2 → ℤ` tuples with positive, mutually dividing first entries and equal products
are equal.** The first entries agree by antisymmetry of divisibility among positives, and the
second is then pinned by cancelling the first out of the product.

Only the *first* entries are assumed positive; the second may be negative or zero. -/
theorem eq_of_dvd_of_dvd_of_mul_eq_mul {a b : Fin 2 → ℤ}
    (ha0_pos : 0 < a 0) (hb0_pos : 0 < b 0) (hab : a 0 ∣ b 0) (hba : b 0 ∣ a 0)
    (hprod : a 0 * a 1 = b 0 * b 1) : a = b := by
  have h0 : a 0 = b 0 :=
    le_antisymm (Int.le_of_dvd hb0_pos hab) (Int.le_of_dvd ha0_pos hba)
  have h1 : a 1 = b 1 :=
    mul_left_cancel₀ (ne_of_gt ha0_pos) (by rw [hprod, h0])
  funext i
  fin_cases i <;> assumption

end

end Int
