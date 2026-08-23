/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The slope of the real exponential at zero

This file records the parameterized right-sided slope limit for `t ↦ exp (a * t)`.  It is a
small shared calculus fact used by both semigroup generator shifts and resolvent calculations.

## Main result

* `TauCeti.tendsto_exp_mul_sub_one_div`: `(exp (a * t) - 1) / t` tends to `a` as `t → 0⁺`.
-/

public section

namespace TauCeti

open Filter

/-- The right-sided difference quotient of `t ↦ exp (a * t)` at zero tends to `a`. -/
theorem tendsto_exp_mul_sub_one_div (a : ℝ) :
    Tendsto (fun t : ℝ => (Real.exp (a * t) - 1) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
  have hderiv : HasDerivAt (fun t : ℝ => Real.exp (a * t)) a 0 := by
    convert ((hasDerivAt_id (x := (0 : ℝ))).const_mul a).exp using 1 <;> simp
  simpa only [zero_add, mul_zero, Real.exp_zero, smul_eq_mul, div_eq_mul_inv,
    mul_comm] using hderiv.tendsto_slope_zero_right

end TauCeti

end
