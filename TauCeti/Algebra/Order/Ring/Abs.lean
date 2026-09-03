/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Absolute values of products with bounded factors

A product is dominated in absolute value by any one factor once the others are bounded by `1`
in absolute value. This is the pointwise estimate behind domination arguments for integrands of
the form `u x * v y * K x y` with `[-1,1]`-valued test functions `u` and `v`.
-/

public section

variable {α : Type*} [Ring α] [LinearOrder α] [IsOrderedRing α] {a b : α}

/-- `|a * b * c| ≤ |c|` whenever `|a| ≤ 1` and `|b| ≤ 1`. -/
theorem abs_mul_mul_le_abs_of_abs_le_one (ha : |a| ≤ 1) (hb : |b| ≤ 1) (c : α) :
    |a * b * c| ≤ |c| := by
  rw [abs_mul, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg c)
    (mul_le_of_le_one_left (abs_nonneg b) ha |>.trans hb))
