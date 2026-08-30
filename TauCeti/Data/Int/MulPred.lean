/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Products of consecutive integers are nonnegative

Over `ℤ` the product `t * (t - 1)` of two consecutive integers is nonnegative, because no integer
lies strictly between `t - 1` and `t`. This is a genuinely integral statement: over `ℝ` it already
fails at `t = 1 / 2`, and over `ℕ` it is vacuous.

The unit-shifted form `0 ≤ s * (s - δ)` for `δ : ℤˣ` follows by rescaling, since the only units of
`ℤ` are `±1` and multiplying by one of them permutes the pair.

## Main results

* `Int.zero_le_mul_sub_one` : `0 ≤ t * (t - 1)`.
* `Int.zero_le_mul_sub_units` : `0 ≤ s * (s - δ)` for a unit `δ`.
-/

public section

namespace Int

/-- Two consecutive integers have nonnegative product: no integer lies strictly between `t - 1`
and `t`. -/
theorem zero_le_mul_sub_one (t : ℤ) : 0 ≤ t * (t - 1) := by
  rcases le_or_gt t 0 with ht | ht
  · nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -t) (by omega : (0 : ℤ) ≤ 1 - t)]
  · exact mul_nonneg (by omega) (by omega)

/-- The exceptional term of a unit exceptional value is nonnegative: rescaling by the unit turns
`s * (s - δ)` into a product of consecutive integers. Nonnegativity fails for the other odd
exceptional values, where already `1 * (1 - ε) < 0` for `ε ≥ 3`. -/
theorem zero_le_mul_sub_units (δ : ℤˣ) (s : ℤ) : 0 ≤ s * (s - (δ : ℤ)) := by
  have hδ : (δ : ℤ) * (δ : ℤ) = 1 := by
    rcases Int.units_eq_one_or δ with rfl | rfl <;> norm_num
  have hEq : ((δ : ℤ) * s) * ((δ : ℤ) * s - 1) = s * (s - (δ : ℤ)) := by
    linear_combination (s * s) * hδ
  rw [← hEq]
  exact zero_le_mul_sub_one _

end Int
