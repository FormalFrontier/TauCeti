/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Periodic

/-!
# The local parameter under translation and period rescaling

Two algebraic identities for the local parameter `𝕢 h z = exp (2 π I z / h)` at a cusp:
translating the argument multiplies by an exponential, and the `m`-th power of the local
parameter at period `m * h` is the local parameter at period `h`.

## Main declarations

* `TauCeti.Periodic.qParam_sub`: `𝕢 h (z - j) = 𝕢 h z * exp (-2 π I j / h)`.
* `TauCeti.Periodic.qParam_nat_mul_pow`: `𝕢 (m * h) z ^ m = 𝕢 h z` for `m ≠ 0`.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public section

open Complex
open scoped Real

namespace TauCeti.Periodic

open Function.Periodic

local notation "𝕢" => Function.Periodic.qParam

variable {h : ℝ}

/-- Translation by `j` in the argument of `qParam` corresponds to multiplication by
`exp (-2 π I j / h)`. -/
theorem qParam_sub (z j : ℂ) : 𝕢 h (z - j) = 𝕢 h z * exp (-2 * π * I * j / h) := by
  simp only [qParam, ← Complex.exp_add]
  ring_nf

/-- The `m`-th power of the local parameter at period `m * h` is the local parameter at
period `h`. -/
theorem qParam_nat_mul_pow {m : ℕ} (hm : m ≠ 0) (z : ℂ) : 𝕢 (m * h) z ^ m = 𝕢 h z := by
  simp only [qParam, ← Complex.exp_nat_mul, ofReal_mul, ofReal_natCast]
  rw [mul_div_assoc', mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hm)]

end TauCeti.Periodic

end
